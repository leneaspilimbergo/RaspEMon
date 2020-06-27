'''
# /usr/bin/python
=================================================================
RaspEMon - RaspberryPi Energy Monitor

(c) 2012 by Luca ENEA-SPILIMBERGO
            luca.enea.spilimbergo@gmail.com
            www.viadellaluna2.it
=================================================================
Storicizza i dati della produzione di un impianto fotovoltaico
leggendo i lampeggi del led del contatore di produzione ENEL
e storicizzando su un database SQLite
Invia email con il riassuntivo della produzione giornaliera
=================================================================

Storia delle revisioni
-----------------------------------------------------------------
0.1    26.08.12	   Prima bozza: lettura lampeggi
0.2    27.08.12    Gestione cambio periodo,giorno,mese
0.3    28.08.12    Salva i dati del periodo su SQLite
0.4    28.10.12    Eliminati i periodi giorno e mese (saranno calcolati con operazioni su DB). 
                   Gestisce potenza max e mancata produzione (led sempre acceso o spento). 
                   Ad ogni periodo aggiorna sul DB i dati giornalieri.
                   Definita funzione per invio messaggi email
0.5    23.12.12    Usa un file di log per gli eventi principali (nella directory dello script)
                   Testate operazioni su DB 
0.6    26.12.12    Invia email quando vede passa da un periodo con produzione ad uno senza (fine) 
                   o viceversa (inizio produzione). 
0.7    28.12.12    Usa un DB diverso per ogni anno, creandolo se non esiste
0.8    21.02.13    Scarta i segnali troppo vicini (superiori a PMax)
0.81   25.02.13    Attende lo spegnimento del led per evitare doppie letture
0.82   26.02.13    Quando scrive nel DB aggiorna sempre i record, per evitare errori nella insert
0.83   27.02.13    Migliorato log lampeggio (indica potenza istantanea a tempo trascorso). Disabilitata email
0.84   28.02.13    Corretto errore, non riprendeva dopo notte a produzione ferma. Riabilitata email
0.85   03.03.13    Crea un nuovo file di log ad ogni avvio (NON CAMBIA OGNI GIORNO)
0.86   07.03.13    Varie modifiche per migliorare robustezza e diagnostica
0.87   09.03.13    Correzione gestione file log giornaliero (NON CAMBIA OGNI GIORNO)
0.88   11.03.13    Corretto formato date nel database (NON VA). Altre modifiche alla gestione log (FUNZIONA)
0.89   12.03.13    Cambiato formato date nel database (ora i campi data sono di tipo TEXT)
0.90   13.03.13    Corretta gestione dati giornalieri nel db
0.91   04.04.13    Aggiunto filtro su dati periodo per evitare false letture a inizio/fine giornata
0.92   30.10.13    Aggiunti 2 campi nella tabella Periods: FasciaEnel (Zone) e stato di upload su EmonCMS (uploaded)
0.93   03.11.13    Inserito delay di 50ms per rilasciare CPU
0.94   19.12.13    Funzione per calcolo fascia Enel, scrive la fascia nel record del periodo
0.95   11.01.14    Scrive dati fascia su tabella Days e Month
0.96   21.02.14    Corregge errori salvataggio DB (troppi periodi) + cambio estensione DB (.s3db) + verifica cambio log al periodo
0.97   28.10.14    Parametri su file di configurazione esterno
0.98   01.01.16    Corregge creazione log al cambio anno

Hardware
------------------------------------------------
led +	res. 470ohm	 su IO1/GPIO18 (pin 11) --R---|<|--- + 3.3V (pin 1)
fotoresistenza 	     su IO0/GPIO17 (pin 12) ------FTR--- GND    (pin 6)
			         IO0 ha anche una resistenza di pull-up da
                     220ohm verso +3.3V
'''

# librerie
# ------------------------------------------------
import time
import RPi.GPIO as GPIO					# Libreria Raspbery GPIO 
import datetime
import os
import sqlite3 as sqlite				# database SQLite3
import sys	
import smtplib							# posta via SMTP
from email.mime.text import MIMEText    # Import the email modules we'll need
import logging                          # gestione logfile
import ConfigParser

CONFIG_VERSION          = "v0.97"


# costanti
# ------------------------------------------------
# constanti da file di configurazione (futura modifica, 22.10.12)
# impostazioni fotovoltaico
config = ConfigParser.RawConfigParser()
config.read('RaspEMon.cfg')
CONFIG_MINUTI_PERIODO 	= config.getint('Period','Duration') 			# durata del periodo di salvataggio (minuti) 
CONFIG_PMAX 			= config.getint('Period','Pmax')				# valore max in W oltre il quale il dato di Pmax viene scartato
# impostazioni varie
CONFIG_ONSCREENDEBUG	= config.getboolean('Various','OnScreenDebug')	# True / False  	
CONFIG_DATABASENAME 	= config.get('Various', 'DatabaseName')			# nome file database sqlite (i segnaposti %Y o simili sono gestiti da datetime.sprintf)
# impostazioni email
CONFIG_MAIL_SMTP_SERVER	= config.get('Mail', 'SMTPserver')				# indirizzo server posta in uscita
CONFIG_MAIL_SMTP_PORT	= config.get('Mail', 'SMTPport')				# porta per server SMTP (GMail = 587)
CONFIG_MAIL_SMTP_SSL	= config.getboolean('Mail','SMTPssl')			# Usa connessione SSL? True / False
CONFIG_MAIL_FROM		= config.get('Mail', 'From')					# usato anche per l'autenticazione SMTP
CONFIG_MAIL_PASSWORD	= config.get('Mail', 'Password')
CONFIG_MAIL_TO			= config.get('Mail', 'To')
CONFIG_LOG_PATH         = config.get('Log', 'Path')						# solo percorso
CONFIG_LOG_FILE         = config.get('Log', 'FileName')					# senza percorso
CONFIG_LOG_LEVEL        = config.getint('Log','Level')

print 'LogLevel=', CONFIG_LOG_LEVEL 

# variabili
# ------------------------------------------------
# strutture per dati energetici
uiDatiPeriodo = 0
uiDatiPeriodoPrecedente = 0
# memorie temporanee
uiPotenza = 0
uiPotenzaMax = 0
uiFTRstato = GPIO.HIGH
uiFTRultimoStato = GPIO.HIGH
# gestione tempo
dtFTRultimoFDS = datetime.datetime.now()
dtFTRprossimoFDS= datetime.datetime.now()
dtAdesso = datetime.datetime.now()
dtPrima = datetime.datetime.now()
iOra=0
iUltimaOra=-1
iMinuto=0
iUltimoMinuto=-1
iPeriodo=0
iUltimoPeriodo=-1
iGiorno=0
iUltimoGiorno=-1
iMese=0
iUltimoMese=-1
iAnno=0
iUltimoAnno=-1
uiFascia=0
sNomeDbPrecedente = ""

# impostazioni GPIO
# ------------------------------------------------
GPIO.setmode(GPIO.BOARD)
GPIO.setup(11, GPIO.OUT)
GPIO.setup(12, GPIO.IN)

# FUNZIONI
# ------------------------------------------------

# apre il file di log con la data attuale            
def ApreLogfile():
    try:
	# controlla se esiste il percorso
	# se non esiste, crea cartella
	folder = datetime.datetime.now().strftime(CONFIG_LOG_PATH)
	if not os.path.exists(folder):
		os.makedirs(folder)
        # nome file
	name = datetime.datetime.now().strftime(CONFIG_LOG_FILE)
        logger = logging.getLogger("RaspEMon")
        logger.setLevel(CONFIG_LOG_LEVEL)
        formatter = logging.Formatter("%(asctime)s %(message)s","%d/%m/%Y %H:%M:%S")
        
	# nome completo (percorso + filename)
	complete_name = folder + name
	# apre il file
	file_handler = logging.FileHandler(complete_name)
        file_handler.setLevel(CONFIG_LOG_LEVEL)
        file_handler.setFormatter(formatter)
        logger.addHandler(file_handler)
    except Exception, e:
        print e

def ChiudeLogfile():
    try:
        logger = logging.getLogger("RaspEMon")
        logger.handlers[0].stream.close()
        logger.removeHandler(logger.handlers[0])
    except Exception, e:
        print e
        
# NomeDatabase - restituisce il nome del database del periodo appena concluso
def NomeDatabase():
    global sNomeDbPrecedente
    try:
        oggi = datetime.date.today()
        nomedb = oggi.strftime(CONFIG_DATABASENAME)
        # deve restituire il nome del DB valido nell'ultimo periodo 
        # per es. alle 00:00 del 1/1/2014 deve scrivere su 20013.db perche' la data/ora corrente sono della fine periodo)
        if (sNomeDbPrecedente == ""):
            sNomeDbPrecedente = nomedb
        else:
            if (sNomeDbPrecedente != nomedb):
                nomedb=sNomeDbPrecedente
            
    except Exception, e:
        logger = logging.getLogger("RaspEMon")
        logger.critical("NomeDatabase - Except = %s", e)
    return nomedb

# DatabaseEsiste - controlla se il file del DB e' presente
def DatabaseEsiste():
    esiste = 0
    try:
        with open(NomeDatabase()) as f: pass
        esiste = 1
    except IOError as e:
        esiste = 0
    return esiste
    
# CreaDatabase - crea un DB vuoto con la struttura pronta
def CreaDatabase():
    sFuncName="CreaDatabase"
    logger = logging.getLogger("RaspEMon")
    try:
        # nome database
        nome_db = NomeDatabase()
        # apre database
        logger.info("%s - crea DB %s", sFuncName, nome_db)
        connessione_db = sqlite.connect(nome_db)
        cursore = connessione_db.cursor()
        cursore.execute("CREATE TABLE [Days] ([Day] TEXT UNIQUE NOT NULL PRIMARY KEY,[Energy] INTEGER NOT NULL,[MaxPower] INTEGER NOT NULL,[F1] INTEGER DEFAULT '0' NULL,[F2] INTEGER DEFAULT '0' NULL,[F3] INTEGER DEFAULT '0' NULL);")
        cursore.execute("CREATE TABLE [Months] ([Month] TEXT UNIQUE NOT NULL PRIMARY KEY,[Energy] INTEGER NOT NULL,[MaxPower] INTEGER NOT NULL,[F1] INTEGER DEFAULT '0' NULL,[F2] INTEGER DEFAULT '0' NULL,[F3] INTEGER DEFAULT '0' NULL);")
        cursore.execute("CREATE TABLE [Periods] ([Date] TEXT UNIQUE NOT NULL PRIMARY KEY,[Energy] INTEGER NOT NULL,[MaxPower] INTEGER NOT NULL,[Zone] INTEGER DEFAULT '1' NULL,[Uploaded] BOOLEAN DEFAULT '0' NULL);")
        connessione_db.commit()
    except sqlite.Error, e:
        # log
        logger.critical("%s - Except = %s", sFuncName, e)
        connessione_db.rollback()
    except Exception, e:
        logger.critical("%s - Except = %s", sFuncName, e)
        
def LeggiDatiMese():
    logger = logging.getLogger("RaspEMon")
    sFuncName="LeggiDatiMese"
    Risultati = []
    try:
        logger.debug("%s", sFuncName)
        # apre database
        nome_db = NomeDatabase()
        logger.debug("%s - apre DB %s", sFuncName, nome_db)
        connessione_db = sqlite.connect(nome_db)
        cursore = connessione_db.cursor()
        # quale intervallo?
        oggi = datetime.date.today()
        intervallo_inizio = datetime.date(oggi.year, oggi.month, 1)
        sSQL = "SELECT SUM(Energy) as Energy, MAX(MaxPower) as MaxPower, SUM(F1) as TotF1, SUM(F2) as TotF2, SUM(F3) as TotF3 FROM Days WHERE Day >= '{}'".format(intervallo_inizio)
        # esegue
        logger.debug("%s - Execute(%s)", sFuncName, sSQL)
        cursore.execute(sSQL)
        connessione_db.commit()
        # recupera i dati
        row = cursore.fetchone()
        for i in range [0,5]:
            Risultati.append(row[i])

    except sqlite.Error, e:
        logger.critical("%s - Except = %s", sFuncName, e)
    except Exception, e:
        logger.critical("%s - Except = %s", sFuncName, e)
    finally:
        # controllo
        for i in range[0,5]:
            print i, Risultati[i]
        return Risultati


def LeggiDatiGiorno():
    logger = logging.getLogger("RaspEMon")
    sFuncName="LeggiDatiGiorno"	
    Risultati = []
    try:
        # apre database
        nome_db = NomeDatabase()
        logger.debug("%s - apre DB %s", sFuncName, nome_db)
        connessione_db = sqlite.connect(nome_db)
        cursore = connessione_db.cursor()
        # quale intervallo?
        oggi = datetime.date.today()
        intervallo_inizio = oggi
        intervallo_fine = oggi + datetime.timedelta(1) 
        sSQL = "SELECT SUM(Energy) as Energy, MAX(MaxPower) as MaxPower FROM Periods WHERE Date BETWEEN '{}' AND '{}'".format(intervallo_inizio.strftime("%Y/%m/%d 00:00"), intervallo_fine.strftime("%Y/%m/%d 00:00"))
        # esegue
        logger.debug("%s - Execute(%s)", sFuncName, sSQL)
        cursore.execute(sSQL)
        connessione_db.commit()
        # recupera i dati
        row = cursore.fetchone()
        Risultati.append(row[0])
        Risultati.append(row[1])
        # legge i dati delle singole fasce
        sSQLbase = "SELECT SUM(Energy) as Tot FROM Periods WHERE (Date BETWEEN '{}' AND '{}') AND zone={}"
        for fascia in range(1,4):
            sSQL = sSQLbase.format(intervallo_inizio.strftime("%Y/%m/%d 00:00"), intervallo_fine.strftime("%Y/%m/%d 00:00"), fascia)
            logger.debug("%s - Execute(%s)", sFuncName, sSQL)
            cursore.execute(sSQL)
            connessione_db.commit()
            row = cursore.fetchone()
            if (row[0]!=None):
                Risultati.append(row[0])
            else:
                Risultati.append(0)
            
    except sqlite.Error, e:
        logger.critical("%s - Except = %s", sFuncName, e)
    except Exception, e:
        logger.critical("%s - Except = %s", sFuncName, e)
    finally:
        return Risultati


# ScriviDatiSuDb
# modo = 1:periodo, 2:giorno, 3:mese
def ScriviDatiSuDB(modo):
    global dtAdesso, dtPrima, uiDatiPeriodo, uiPotenzaMax, uiFascia
    logger = logging.getLogger("RaspEMon")
    sFuncName="ScriviDatiSuDb"
    try:
        logger.debug("%s - modo = '%s'", sFuncName, modo)
        # controlla se esiste il db
        nome_db = NomeDatabase()
        if (not(DatabaseEsiste())):
            # crea il database
            CreaDatabase()
        # apre database
        logger.debug("%s - apre DB %s", sFuncName, nome_db)
        connessione_db = sqlite.connect(nome_db)
        # periodo
        if(modo==1):
            # salva i dati del periodo
            cursore = connessione_db.cursor()
            sSQL = "INSERT OR REPLACE INTO Periods VALUES('{}',{},{},{},0)".format(dtAdesso.strftime("%Y/%m/%d %H:%M:%S"), uiDatiPeriodo, uiPotenzaMax, uiFascia)
            logger.debug("%s - Execute(%s)", sFuncName, sSQL)
            cursore.execute(sSQL)
            connessione_db.commit()

        # giorno
        if((modo==2) or (modo==1)):
            # legge da Periods i dati di oggi
            results = LeggiDatiGiorno()
            # aggiorna il valore nella tabella Days
            cursore = connessione_db.cursor()
            sSQL="INSERT OR REPLACE INTO Days VALUES('{}',{},{},{},{},{})".format(dtAdesso.strftime("%Y/%m/%d"), results[0], results[1], results[2], results[3], results[4])
            logger.debug("%s - Execute(%s)", sFuncName, sSQL)
            cursore.execute(sSQL)
            connessione_db.commit()
        # mese
        if((modo==3) or (modo==2)):
            # aggiorna il valore nella tabella Months
            # TODO: deve farlo solo per il mese corrente
            cursore = connessione_db.cursor()
            sSQL="insert or replace into Months select substr(Days.Day,1,7) as Month, SUM(Energy) as Energy, MAX(MaxPower) as MaxPower, SUM(F1) as F1, SUM(F2) as F2, SUM(F3) as F3 from Days GROUP BY substr(Days.Day,1,7)"
            logger.debug("%s - Execute(%s)", sFuncName, sSQL)
            cursore.execute(sSQL)
            connessione_db.commit()
    except sqlite.Error, e:
        # log
        logger.critical("%s - Except = %s", sFuncName, e)
        connessione_db.rollback()
    except Exception, e:
        logger.critical("%s - Except = %s", sFuncName, e)

        
# InviaEmail - invia il testo indicato per posta elettronica
def InviaEmail(oggetto, testo):
    logger = logging.getLogger("RaspEMon")
    sFuncName = "InviaEmail"
    try:
        logger.debug("%s: %s", sFuncName, oggetto)
        msg = MIMEText(testo)
        msg['Subject'] = oggetto
        msg['From']=CONFIG_MAIL_FROM
        msg['To'] = CONFIG_MAIL_TO
        # Send the message via gmail SMTP server
        s = smtplib.SMTP(CONFIG_MAIL_SMTP_SERVER, CONFIG_MAIL_SMTP_PORT)
        s.ehlo()
        if (CONFIG_MAIL_SMTP_SSL): s.starttls()
        s.login(CONFIG_MAIL_FROM, CONFIG_MAIL_PASSWORD)
        # Python 3.2.1
        s.send_message(msg)
        logger.debug("%s: Inviata (python 3.x): '%s'", sFuncName, oggetto)
        s.close()
    except AttributeError:
        # Python 2.7.2
        s.sendmail(msg['From'], [msg['To']], msg.as_string())
        s.quit()
        logger.debug("%s: Inviata (python 2.x): '%s'", sFuncName, oggetto)
    except Exception, e:
        logger.critical("%s - Except = %s", sFuncName, e)
 

# InviaEmailDatiProduzione - invia i dati della produzione giornaliera
def InviaEmailDatiProduzione(stato):
    try:
        # prepara il testo standard
        oggetto = "Fotovoltaico: " + stato + " produzione"
        if (stato=="inizio"):
            testo = "Avvio produzione impianto\r\n" 
        if (stato=="fine"):
            testo = "Fine produzione impianto\r\n"
            results = LeggiDatiGiorno("giorno")
            testo += "Produzione odierna: {}Wh (PMax={}W)\r\nF1={}Wh, F2={}Wh, F3={}Wh\r\n".format(results[0], results[1],results[2],results[3],results[4])
            results = LeggiDatiMese("mese")
            testo += "Produzione mensile: {}Wh (PMax={}W)\r\nF1={}Wh, F2={}Wh, F3={}Wh\r\n".format(results[0], results[1],results[2],results[3],results[4])
        InviaEmail(oggetto, testo)   
    except Exception, e:
        logger = logging.getLogger("RaspEMon")
        logger.critical("InviaEmailDatiProduzione - Except = %s", sFuncName, e)

# calcola la fascia ENEL di appartenenza
def FasciaEnel(dtPeriodo):
    iOra = dtPeriodo.hour
    iGiornoSettimana = dtPeriodo.isoweekday() #1=lun, 7=dom
    iFascia=0
    #print "giorno_settimana=", iGiornoSettimana
    #print "ora=", iOra
    # lun-ven
    if ((iGiornoSettimana >= 1) and (iGiornoSettimana <=5)):
        if ((iOra>=8) and (iOra<=18)):
            iFascia=1
        else:
            if ((iOra==7) or ((iOra>=19) and (iOra<23))):
                iFascia=2
            else:
                iFascia=3
    # sab
    if (iGiornoSettimana==6):
        if ((iOra>=7) and (iOra<23)):
            iFascia=2
        else:
            if (((iOra>=0) and (iOra<7)) or (iOra>=23)):
                iFascia=3
    # domenica
    if (iGiornoSettimana==7):
        iFascia=3
    # casi speciali
    giorni_speciali = ["0101","0601","2504", "0105", "0206", "1508", "0111", "0812", "2512", "2612"]
    giorno_attuale = dtPeriodo.strftime("%d%m")
    if (giorno_attuale in giorni_speciali):
        iFascia=3
    # fine
    return iFascia
        
# ControlloCambio - controlla se e' cambiato il periodo/ora/giorno
def ControlloCambio():
    logger = logging.getLogger("RaspEMon")
    try:
    	# variabili
        global dtPrima, dtAdesso, iOra, iMinuto, iUltimaOra, iUltimoMinuto
        global iGiorno, iMese, iUltimoGiorno, iUltimoMese, iAnno, iUltimoAnno
        global iPeriodo, iUltimoPeriodo, uiDatiPeriodoPrecedente, uiFascia
        global uiDatiPeriodo, uiDatiGiorno, uiDatiMese, uiPotenzaMax
        # salva orario precedente
        dtPrima = dtAdesso
        # legge orario attuale
        dtAdesso = datetime.datetime.now()
        iOra = dtAdesso.hour
        iMinuto = dtAdesso.minute
        iGiorno = dtAdesso.day
        iMese = dtAdesso.month
        iAnno = dtAdesso.year
        iPeriodo=Periodo(iMinuto, iOra)
        # cambio?
        if (iOra != iUltimaOra):
        	iUltimaOra=iOra
        if (iMinuto != iUltimoMinuto):
        	iUltimoMinuto = iMinuto
        # cambio periodo?
        if (iPeriodo != iUltimoPeriodo):
            try:
                # (eventualmente) passa a nuovo log
                ChiudeLogfile()
                ApreLogfile()
                # filtro per dati errati
                if ((uiDatiPeriodo==1) and (uiPotenzaMax==0)):
                    uiDatiPeriodo=0
                # quale fascia?
                uiFascia = FasciaEnel(dtPrima)
                # log
                logger.debug("Cambio periodo: %i->%i", iUltimoPeriodo, iPeriodo)
                logger.info("Fine periodo %i. Energia=%iWh, PMax=%iW, Fascia=%i", iUltimoPeriodo, uiDatiPeriodo,uiPotenzaMax, uiFascia)
                # salva i dati del periodo
                if (iUltimoPeriodo != -1):
                    ScriviDatiSuDB(1)
                # conferma ultimo periodo
                iUltimoPeriodo = iPeriodo
                # controlla se deve inviare email
                if ((uiDatiPeriodoPrecedente == 0) and (uiDatiPeriodo != 0)):
                    InviaEmailDatiProduzione("inizio")
                if ((uiDatiPeriodoPrecedente != 0) and (uiDatiPeriodo == 0)):
                    InviaEmailDatiProduzione("fine")
                # azzera i dati del nuovo periodo
                uiDatiPeriodoPrecedente = uiDatiPeriodo
                uiDatiPeriodo = 0
                uiPotenzaMax = 0
                logger.debug("Azzerati dati periodo");
            except Exception, e:
                logger.critical("ControlloCambio - Except = %s", sFuncName, e)
                iUltimoPeriodo = iPeriodo
        # cambio giorno?
        if (iGiorno != iUltimoGiorno):
            # salva i dati del giorno
            if (iUltimoGiorno!=-1): ScriviDatiSuDB(2)
            # azzera i dati del nuovo giorno
            uiDatiGiorno=0
            # fatto
            iUltimoGiorno=iGiorno
        # cambio mese?
        if (iMese != iUltimoMese):
            # salva i dati del mese
            if (iUltimoMese!=-1): ScriviDatiSuDB(3)
            # azzera i dati del nuovo mese
            uiDatiMese=0
            # fatto
            iUltimoMese=iMese
    except Exception, e:
            logger.critical("ControlloCambio - Except = %s", sFuncName, e)


# Periodo - calcolo numero periodo all'interno del giorno
def Periodo(minuto, ora):
	global CONFIG_MINUTI_PERIODO
	return ((minuto + ora*60) / CONFIG_MINUTI_PERIODO)

   
# LeggiIngressoENEL - legge segnale dalla fotoresistenza
def LeggiIngressoENEL():
    logger = logging.getLogger("RaspEMon")
    global uiFTRstato, uiFTRultimoStato
    global dtFTRultimoFDS, dtFTRprossimoFDS
    global uiDatiPeriodo, uiDatiGiorno, uiDatiMese, uiPotenza, uiPotenzaMax
    try:
        uiVal = 0
    	# tempo attuale?
        dtAdesso = datetime.datetime.now()
        dtTempoPassato = dtAdesso - dtFTRultimoFDS # default
    	# legge ingresso
        uiFTRstato = GPIO.input(12)
    	# cambiato? 
        if (uiFTRstato!=uiFTRultimoStato): 
    		# salva nuovo stato 
            uiFTRultimoStato=uiFTRstato 
    		# il led del contatore e' acceso (ingresso Pi basso)
            if (uiFTRstato==GPIO.LOW):
    			# tempo trascorso
                dtTempoPassato = dtAdesso - dtFTRultimoFDS
    			# potenza instantanea (Wh)
                msPassati = (dtTempoPassato.seconds*1000 + dtTempoPassato.microseconds/1000)
                uiVal = 3600000 / msPassati # Wh
    			# dato valido?
                if (uiVal>0) and (uiVal<CONFIG_PMAX ):
    				# incrementa dati (kW)
                    uiDatiPeriodo += 1
                    uiDatiGiorno += 1
                    uiDatiMese += 1
    				# salva il valore di potenza istantanea
                    uiPotenza = uiVal
    				# salva il valore di potenza max del periodo
                    if ((uiPotenza > uiPotenzaMax) and (uiDatiPeriodo > 1)): uiPotenzaMax = uiPotenza
                    # ok
                    logger.debug("(IN)->OK (P=%i, t=%i)", uiVal, msPassati)
                else:
                    logger.debug("(IN)     (P=%i, t=%i)", uiVal, msPassati)
    		    # prossimo timestamp atteso
                dtFTRprossimoFDS = dtAdesso + dtTempoPassato * 4
                # led diagnostico acceso
                GPIO.output(11, GPIO.LOW)
                # attende che si spenga il led per evitare doppie letture
                while (GPIO.input(12) == GPIO.LOW):
                    time.sleep(0.05)
                    ControlloCambio()
                # memorizza timestamp
                dtFTRultimoFDS = datetime.datetime.now()
            else:
                # led diagnostico spento
                GPIO.output(11, GPIO.HIGH)
        else:
            # non cambia da troppo tempo?
            if (dtAdesso > dtFTRprossimoFDS):
                # niente produzione (led sempre spento o sempre acceso)
                uiPotenza = 0
    except Exception, e:
        logger.critical("LeggiIngressoENEL - Except = %s", sFuncName, e)
            
def Init():
    try:
        ApreLogfile()
        logger = logging.getLogger("RaspEMon")
        logger.info('Avvio RaspEMon...')
        logger.info(CONFIG_VERSION)
        # spegne il led
        GPIO.output(11, GPIO.HIGH)
    except Exception, e:
        print e

            
# ------------------------------------------------
# PROGRAMMA    
# ------------------------------------------------
# inizializzazioni varie
Init()
# invia email per notificare l'avvio
InviaEmail("Avvio RaspEMon", "Il programma RaspEMon e' stato avviato")
# ciclo principale
while True:
	try:
		ControlloCambio()
		LeggiIngressoENEL()
		time.sleep(0.05)
		if (CONFIG_ONSCREENDEBUG):
			os.system('clear')    
			print "RaspEMon"
			print "================================================="
			print "Data/ora           =", dtAdesso 
			print "Periodo            =", iPeriodo
			print "UltimoPeriodo      =", iUltimoPeriodo
			print "Produzione Periodo =", uiDatiPeriodo, "Wh"
			print "Potenza instantanea=", uiPotenza, "W"
			print "FDS:         ultimo=", dtFTRultimoFDS
			print "           prossimo=", dtFTRprossimoFDS
	except Exception, e:
		print e
        
