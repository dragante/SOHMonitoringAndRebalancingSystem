#include <Wire.h>
#include <Adafruit_ADS1X15.h>
#include <MemoryFree.h>;
#include <pgmStrToRAM.h>;

unsigned long tiempoactual, tiempopreviomuestreo, tiempoprevioram, SegundosEjecucion;
const unsigned long TIEMPOMUESTREOMSEG = 2000;
const unsigned long TIEMPORAM = 30000;
const uint32_t TIEMPOMUESTREOSEG = 2; // Tiempo de muestreo en segundos
int retmuestras;
const unsigned long NUMCHARMUESTRAS = 75;
const unsigned long NUMCHARFINCARGA = 50;
static char muestras[NUMCHARMUESTRAS];
char szF1[30];
char szF2[30];

bool firstCycle = false;
// Tiempo de descarte de épocas: 2 minutos (en milisegundos), tiempo para descartar subidas y bajadas del cambio de un ciclo a otro
const unsigned long TIEMPODESCARTE = 120000;
// En lugar de ser 2 minutos, como al inicio solo hay carga, sería la mitad. Lanzar putty a la vez para no perder tiempo!
const unsigned long TIEMPOINICIODESCARTE = 60000;

//******************************************
// **********     VARIABLES Y CONSTANTES      **********
//******************************************
//Baudrate serie posible para comunicación entre el USB de Arduino y el PC o Raspberry
const long SERIALSPEED = 9600;
//Tamaño del vector para calcular la media. Configurado a valor 3 pues lo pidió Edgar el día 4/5/2023 (con derivada media de 3 valores tambien)
const int NUMELEMARRAY = 7;
const int NUMELEMDER = 7;
float multiplier = 0.125F; /* ADS1115   +/- 4.096V  1 bit = 2mV      0.125mV (16-bit results) */
float ADCOutputVoltageActual;
float arrayADC[NUMELEMARRAY]; // Vector para almacenar los últimos 4 valores del ADC y luego hacer una media
float arrayMEDIA[NUMELEMDER]; // Idem para la derivada
//Tamaño del vector para el número de periodos de carga/descarga a almacenar
const int NUMCYCLESLIMIT = 1000;
float media = 0;
float mediaprevia = 0;
float derivadamedia = 0;
int intderivadamedia = 0;
float derivadamediaprevia = 0;
//********** Variables para calcular la media temporal y así evitar picos **********
//ADC ADS1115 in differential mode returns a 16 bit integer
int16_t salidaADC;
int contadorMedia = 0;
int contadorMediaDerivada = 0;
// Cálculo de la derivada
float derivadaSimple = 0;
float derivadaMin = 10000; // Lo iniciamos a un valor alto para evitar que se quede con el cero
int contadorMinTemp = 0;
int arrayderivadamintemp[3];
int contderivadamintemp[3];
float LIMITEDESCARTE = 10.0; // Con valores menores da falsos positivos
float valorcortefincarga = 0.0;

// Máquina estados Carga Descarga
int SOCState = 0; // 0 -> Aún sin computar tras inicio; 1 -> Carga; 2 -> Descarga;
int numCiclos = 1; // Número de ciclos desde el inicio del programa (siempre se ha de iniciar en carga)
unsigned long epocaInicioCarga = 0;
unsigned long epocaInicioDescarga = 0;
unsigned long periodoCicloCargaActual = 0;
unsigned long periodoCicloDescargaActual = 0;
unsigned long periodoCicloCargaPrevio = 0;
unsigned long periodoCicloDescargaPrevio = 0;
int numSemiciclosCarga = 0;
int numSemiciclosDescarga = 0;
float derivadasMinimasCarga[NUMCYCLESLIMIT];
bool DescartarMinimo = true; // inicia a true por el primer ciclo de carga
unsigned long tiemporeferenciaderivada, tiemporeferenciatransicion;
short contadorCiclosDerTrans;

// Constantes y variables máquina estados rebalanceo
bool EstadoBalanceador = false; // al arrancar el programa, el balanceador está desactivado por defecto
int numTotalBal = 0; // número total de veces que se ha completado un rebalanceo
bool EnableTest1,EnableTest2;
bool ConditionTest1,ConditionTest2;
bool fromDischargeToCharge = false;
bool fromChargeToDischarge = false;
bool Test7FlagOn = false;
float fpercdiff = 0.0; // Puede ser positivo
int ipercdiff = 0;  // Puede ser positivo
//Si el porcentaje baja de este minimo, iniciar rebalanceo
const int PERCENTAGEPERIODMIN = 95;
//Tiempo en milisegundos para el delay inicial del balanceador (10 minutos --> 10 x 60 x 1000ms)
const long DELAYTIMEREBALANCEON = 600000;
//Tiempo en milisegundos para el directo, lo dejamos en 1 minuto para evitar que rebalancee al final de la carga (60 x 1000 ms ) = 60000
const long DIRECTOTIMEREBALANCEON = 60000;
//Tiempo en milisegundos para aplicación fija del balanceador (12 minutos --> 12 x 60 x 1000ms)
const long BALONINTERVALTIME = 720000;
//Tiempo en milisegundos para aplicación fija del balanceador 1 minuto (1 --> 1 x 60 x 1000ms)
const long BALONINTERVALTIMEONE = 60000;
//Tiempo en milisegundos antes de terminar la carga (10 minutos --> 10 x 60 x 1000ms)
const long LASTINTERVALTIME = 600000;
unsigned long currentMillis = 0;    // stores the value of millis() in each iteration of loop()
unsigned long prevDelayBalOnMillis = 0;
unsigned long prevIntervalBalOnMillis = 0;
unsigned long inicioUltimoSemicicloCarga = 0;
int DuracionUltimoPeriodoCarga = 0;
int longestChargePeriod = 0;
float derivadaminhistorica = 100.0; //IMPORTANTE: HAY QUE INICIALIZAR ESTE VALOR A 100.0 PARA QUE LUEGO LO COMPARE Y LOS VAYA GUARDANDO
float mediaderivada3_4_5 = 0.0;
float derivadaminactual,derivadaminactual_100, derivadaminhistorica100, divactualreferencia, divactualreferencia100,diferenciaderivada;
long derivadaminhistoricaint, derivadaminactualint, divactualreferenciaint, diferenciaderivadaint;
 
bool rebalanceoderivadamin = false;
//Si el porcentaje diferencia es mayor que este valor, iniciar rebalanceo
// 09/05/2024: porcentaje cambiado de 10 a 5 por petición de Edgar
const long PERCENTAGEDERMIN = 5;
int lastBalChargeSemicycle = 0; //Para esperar un ciclo tras un rebalanceo
int numCiclos2V; // Para saber cuándo corto a 1,6V o a 2V. Se establece en la config()
int numelemmediaderref;

// Activar o desactivar modo debugueo
bool modoDebug; // 0 desactivado, 1 activado

// Para contar el tiempo de ejecución y mostrarlo en el el log
short segundos, minutos, horas, dias;

// Estados para la detección del ciclo
enum estadoCargaDescarga {
  INICIO,
  CARGA,
  DESCARGA,
};

// Estados para descartar transiciones
enum estadoTransicion {
  INICIOPRIMERCICLOCARGA,
  NOTRANSICION,
  TRANSICION,
};

// Estados para aplicar el balanceador de forma normal
enum transicionesBal {
INIT,
DELAY,
LAST10,
BALANCING,
DIRECT,
BALANCINGONEMIN
};

// Instancia para la detección del periodo, con inicialización
estadoCargaDescarga ecd = INICIO;

// Instancia para la detección del periodo, con inicialización
estadoTransicion trn = INICIOPRIMERCICLOCARGA;

// Instancia para el retraso y activación del balanceador en modo normal, con inicialización
transicionesBal estadoBal = INIT;

//******************************************
// **********     ENTRADA/S       **********
//******************************************
// Instancia concreta del ADS que va a la batería de flujo redox. Numerado como "_1" por si añadimos más en el futuro
Adafruit_ADS1115 ads1115_Bateria;

//******************************************
// **********     SALIDA/S       **********
//******************************************
//Se ha seleccionado como salida del autómata el PIN 42, que equivale al Relay R1.8 (salida digital)
int SALIDA_BALANCEADOR = 42;

//*************************************************
// ***** FUNCIONES PARA ORGANIZAR EL CÓDIGO  ******
//*************************************************
/*
 * Activa/desactiva el balanceador cuando es necesario
 * 
 */
void Balanceador() {

  // Primero definimos las condiciones de cada test a ejecutar
  // Para activar un test y desactivar los demás, ir a setup()

  /* TEST 1
     Creado el 15/03/2024 para cuando cortamos unos voltios a 2V. Sólo se rebalancea al final del ciclo después del último a 2V. Se espera un ciclo entre rebalanceos. 
     El lastBalChargeSemicycle == 1 es para que pueda entrar el primer ciclo si se quitara la condición "numSemiciclosCarga >= numCiclos2V"
  */
  ConditionTest1 =  EnableTest1 &&
                    fromChargeToDischarge &&
                    numSemiciclosCarga > numCiclos2V &&
                    divactualreferenciaint >= PERCENTAGEDERMIN && 
                    (lastBalChargeSemicycle == 1 || ((numSemiciclosCarga - lastBalChargeSemicycle) > 1));

  /* TEST 2
     Creado el 04/04/2024 según lo dicho por Edgar pues mañana relanzamos con batería remontada. 
     Se espera un ciclo entre rebalanceos.
  */
  ConditionTest2 =  EnableTest2 &&
                    fromChargeToDischarge &&
                    divactualreferenciaint >= PERCENTAGEDERMIN && 
                    ((numSemiciclosCarga - lastBalChargeSemicycle) > 1);

  switch (estadoBal) {
    // INIT: el balanceador está desactivado, esperamos a que cambie el periodo lo establecido
    case INIT:

      digitalWrite(SALIDA_BALANCEADOR,LOW);
      EstadoBalanceador = false;
      
      // TEST 1
      if (ConditionTest1 or ConditionTest2) {

        // Actualizamos el valor del DELAY previo al balanceo para iniciar la referencia de tiempo para el siguiente estado
        prevDelayBalOnMillis = currentMillis;

        // Almacenamos como referencia el semiciclo actual de carga
        lastBalChargeSemicycle = numSemiciclosCarga;
         
        estadoBal = DIRECT;
      }

      break;
    // DELAY: esperamos un tiempo antes de activar el balanceador (balanceador sigue desactivado en este estado)
    case DELAY:

      digitalWrite(SALIDA_BALANCEADOR,LOW);
      EstadoBalanceador = false;
      
      if ((currentMillis - prevDelayBalOnMillis) >= DELAYTIMEREBALANCEON) {
        
        // Actualizamos el valor del INTERVALO de balanceo para iniciar la referencia de tiempo para el siguiente estado que es el balanceo
        prevIntervalBalOnMillis = currentMillis; 
        
        estadoBal = BALANCING;
      }
      
      break;

    // LAST10: esperar a que queden 10 minutos del ciclo de carga
    case LAST10:

      digitalWrite(SALIDA_BALANCEADOR,LOW);
      EstadoBalanceador = false;

      // Ponemos en una variable el valor del periodo del ultimo ciclo de carga que ha terminado
      //DuracionUltimoPeriodoCarga = periodosCarga[numSemiciclosCarga];
      
      if (currentMillis >= (DuracionUltimoPeriodoCarga - LASTINTERVALTIME - inicioUltimoSemicicloCarga)) {

        // Actualizamos el valor del INTERVALO de balanceo para iniciar la referencia de tiempo para el siguiente estado que es el balanceo
        prevIntervalBalOnMillis = currentMillis;    
    
        estadoBal = BALANCING;
      }
      
      break;
      
    // BALANCING: activamos el balanceador, y a los 10 minutos volvemos al estado reposo inicial con el balanceador desactivado
    case BALANCING:

      digitalWrite(SALIDA_BALANCEADOR,HIGH);
      EstadoBalanceador = true;

      if ((currentMillis - prevIntervalBalOnMillis) >= BALONINTERVALTIME) {

        // Contador de número de veces que se rebalanceado la batería
        numTotalBal = numTotalBal + 1;
        
        estadoBal = INIT;
      }
      
      break;

    // DIRECT: apenas aplicamos delay para así rebalancear sólo en la descarga y al inicio
    case DIRECT:

      digitalWrite(SALIDA_BALANCEADOR,LOW);
      EstadoBalanceador = false;
      
      if ((currentMillis - prevDelayBalOnMillis) >= DIRECTOTIMEREBALANCEON) {
        
        // Actualizamos el valor del INTERVALO de balanceo para iniciar la referencia de tiempo para el siguiente estado que es el balanceo
        prevIntervalBalOnMillis = currentMillis; 
        
        estadoBal = BALANCINGONEMIN;
      }
      
      break;

    // BALANCINGONEMIN: activamos el balanceador pero esta vez sólo durante 1 minuto para no pasarnos
    case BALANCINGONEMIN:

      digitalWrite(SALIDA_BALANCEADOR,HIGH);
      EstadoBalanceador = true;   

      if ((currentMillis - prevIntervalBalOnMillis) >= BALONINTERVALTIMEONE) {

        // Contador de número de veces que se rebalanceado la batería
        numTotalBal = numTotalBal + 1;

        // Para debuguear
        Serial1.print(F("\nSe acaba de apagar el rebalanceador tras 1 minuto encendido en el ciclo: : "));
        Serial1.print(numCiclos);
        Serial1.print(F("\n"));

        // Para debuguear
        Serial1.print(F("\nNumero actual de rebalanceos: "));
        Serial1.print(numTotalBal);
        Serial1.print(F("\n"));
        
        estadoBal = INIT;
      }

    default:
      ;
  } 
  
}

// Calculo de la media del voltaje e impresión en consola, y cálculo de la derivada
void MediaVoltajeyDerivada () {

  // Rellenamos el vector
  if(contadorMedia < NUMELEMARRAY){
    arrayADC[contadorMedia] = ADCOutputVoltageActual;
    contadorMedia++;
  }
  else
  {  
    for(int i = 0; i < (NUMELEMARRAY-1); i++){
      arrayADC[i] = arrayADC[i + 1];
    }
    arrayADC[(NUMELEMARRAY-1)] = ADCOutputVoltageActual;
  }
   
  // Imprimo todo el array para ver qué voy guardando
  /*Serial1.print(" V: [ ");
  for(int i = 0; i <= (NUMELEMARRAY-1); i++){
    Serial1.print(arrayADC[i]);
    Serial1.print(",");
  }
  Serial1.print(" ]");*/
  /////////////////////////////////////////////

  // Para debuguear, antes de calcular a media, imprimo el valor medio previo
  //Serial1.print(" V p: ");
  //Serial1.print(mediaprevia);

  /////////////////////////////////////////////
  // Calculo la media 
  media = 0;
  for(int i = 0; i < NUMELEMARRAY; i++){
    media = media + arrayADC[i];
  }
  media = media / NUMELEMARRAY;
  // Imprimo la media
  //Serial1.print(" V m: ");
  //Serial1.print(media);
  /////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////
  // Cálculo de la derivada sobre el valor medio
  derivadaSimple = abs(media - mediaprevia)/TIEMPOMUESTREOSEG;
  //  Imprimo la derivada
  //Serial1.print(" D abs (mV): ");
  //Serial1.print(derivadaSimple);
    
  // Actualizamos el valor previo de la media del ADC para el cálculo de la derivada
  mediaprevia = media;
}

// Calculo de la media de la derivada
void DerivadaMedia() {

    /////////////     MEDIA DERIVADA ///////////////////////////
    // Guardar valores en array de media
    if(contadorMediaDerivada < NUMELEMDER){
      arrayMEDIA[contadorMediaDerivada] = derivadaSimple;
      contadorMediaDerivada++;
    }
    else
    {  
      for(int i = 0; i < (NUMELEMDER-1); i++){
        arrayMEDIA[i] = arrayMEDIA[i + 1];
      }
      arrayMEDIA[(NUMELEMDER-1)] = derivadaSimple;
    }
   
    // Imprimo todo el array para ver qué voy guardando
    /*Serial1.print(" Array D med: [ ");
    for(int i = 0; i <= (NUMELEMDER-1); i++){
      Serial1.print(arrayMEDIA[i]);
      Serial1.print(",");
    }
    Serial1.print(" ]");*/
    /////////////////////////////////////////////

    // Para debuguear, antes de calcular la derivada media, imprimo la derivada previa
    //Serial1.print(" D p: ");
    //Serial1.print(derivadamediaprevia);

    /////////////////////////////////////////////
    // Calculo la media de la DERIVADA
    derivadamedia = 0;
    for(int i = 0; i < NUMELEMDER; i++){
      derivadamedia = derivadamedia + arrayMEDIA[i];
    }
    derivadamedia = derivadamedia / NUMELEMDER;
    // Imprimo la derivada media
    /*Serial1.print(" D media: ");
    Serial1.print(derivadamedia);
    /////////////////////////////////////////////

    // Para debuguear la derivada minima en cada epoca
    Serial1.print(" D min: ");
    Serial1.print(derivadaMin);

    // Para debuguear estados
    Serial1.print(" Tiempo act: ");
    Serial1.print(tiempoactual);

    // Para debuguear el bool de descartar
    Serial1.print(" Caso trn: ");
    Serial1.print(trn);*/

    // Actualizamos el valor previo de la derivada media
    derivadamediaprevia = derivadamedia;  
}

//////////////////////////////////////////////////////
// Función creada el 8/5/2023 tras reunión con Edgar: descartaremos el mínimo en las transiciones, pues nos interesa el del entorno del 50% para el estado de salud
void DescartarTransicionesSOC() {
  
  switch (trn) {

    // Estado trn == 0 --> Inicio primer ciclo de carga, se descarta un tiempo
    case INICIOPRIMERCICLOCARGA:

      DescartarMinimo = true;

      if ( (tiempoactual - tiemporeferenciatransicion) > TIEMPOINICIODESCARTE) {

        /*Serial1.println("\n Fin de descarte primer ciclo carga. Tiempo pasado: ");
        Serial1.print(tiempoactual);
        Serial1.print(" Tiempo transicion: ");
        Serial1.print(tiemporeferenciatransicion);*/

        // Cambiamos de estado
        trn = NOTRANSICION;  
      }

    break;
    
    // Estado trn == 1 --> estamos en una carga sin transiciones y queremos detectar el mínimo
    case NOTRANSICION:

      DescartarMinimo = false;

      // Si se detecta que la derivada es mayor de un límite durante tres ciclos consecutivos
      if (derivadaSimple >= LIMITEDESCARTE) {
        
        contadorCiclosDerTrans++;

        if (contadorCiclosDerTrans == 3) {

          // Reseteamos el contador
          contadorCiclosDerTrans = 0;

          // Guardo la referencia de tiempo
          tiemporeferenciaderivada = millis();

          // Para debuguear
          /*Serial1.println("\nDetectada transicion: a partir de ahora, NO se guarda derivada minima. ");
          Serial1.print(" Tiempo de referencia: ");
          Serial1.print(tiemporeferenciaderivada);
          Serial1.println(" Tiempo actual: ");
          Serial1.print(tiempoactual);*/
          
          trn = TRANSICION;
        }
      }
      // Descontar si de repente no se cumple
      if (contadorCiclosDerTrans >=1 && derivadaSimple < LIMITEDESCARTE) {
        contadorCiclosDerTrans--;    
      }
    
    break;
    
    // Estado trn == 2 --> se ha detectado una transición, así que no guardamos el mínimo por las oscilaciones en la derivada
    case TRANSICION:

      // Activamos esta flat para no guardar el valor en la carga en MaquinaEstadosCD()
      DescartarMinimo = true;

      if ( (tiempoactual - tiemporeferenciaderivada) > TIEMPODESCARTE ) {

        // Almaceno la referencia de la transicion para coherencia con el estado 0
        tiemporeferenciatransicion = millis();
        
        /*Serial1.println("Fin transicion: ahora sí guardamos derivada minima. Tiempo actual: ");
        Serial1.print(tiempoactual);
        Serial1.println("Tiempo transicion: ");
        Serial1.print(tiemporeferenciatransicion);*/

        // Cambiamos de estado
        trn = NOTRANSICION;
                 
      }

    break;

    // En cualquier otro caso
    default:
      Serial1.println("ERROR 2: estado no contemplado! ");
  }  
}

void MaquinaEstadosCD() {
  
  switch (ecd) {
    
    // Reseteo de la máquina de estados
    case INICIO:

      // Reseteamos variables
      fromDischargeToCharge = false;
      fromChargeToDischarge = false;

      // Arrancamos en 0
      SOCState = 0;
   
      epocaInicioCarga = SegundosEjecucion;

      // Cambiamos a carga siempre al inicio, pues hay que arrancarlo cuando se inicia una carga en el BTS
      ecd = CARGA;
    
    break;
    
    // Semiciclo de carga
    case CARGA:

      // Reseteamos el flag
      fromDischargeToCharge = false;

      // Estamos en carga
      SOCState = 1;

      // Nos quedamos con el valor mínimo, descartando el inicio del primer ciclo de carga y las transiciones
      if ( (derivadamedia < derivadaMin) and (not DescartarMinimo) ) {
        derivadaMin = derivadamedia;  
      }

      ///////////  FIN DE ALGORITMO   /////////////////////////////////////////////////////////////////
      /////////////////////////////////////////////////////////////////////////////////////////////////

      // Según el nº de ciclos a 1,6V o a 2V, considero corte diferente, para luego rebalancear siempre en descarga
      if (EnableTest1 and (numSemiciclosCarga <= numCiclos2V)){
        // Ojo, este valor tiene que ser bastante menor de 2000, pues la media solo llega 1850, para que cuente bien los periodos
        valorcortefincarga = 1750.0;
      }
      else {
        valorcortefincarga = 1550.0;           
      }
      
      // PASO DE CARGA A DESCARGA, es decir, termina un ciclo de carga, en mV
      if (ADCOutputVoltageActual > valorcortefincarga){

        // Flag para señalizar otras partes del código
        fromChargeToDischarge = true;

        // Incrementamos el valor de los ciclos
        numSemiciclosCarga = numSemiciclosCarga + 1;
        
        // Almaceno el periodo anterior para compararlo más adelante
        periodoCicloCargaPrevio = periodoCicloCargaActual;
        
        // Almaceno el periodo actual
        periodoCicloCargaActual = SegundosEjecucion - epocaInicioCarga;
         
        // Si estamos fuera de una transición, almacenamos la derivada minima del ciclo actual para tener histórico,
        derivadasMinimasCarga[numSemiciclosCarga] = derivadaMin;  
        
        /////////////////////////////////////////////////////////////////////////////
        // 15/03/2024: Nuevo algoritmo para activación del rebalanceador con la derivada.
        // Al final del último ciclo a 2V, recorremos los ciclos 3,4 y 5 y hacemos la media, que será la derivada histórica (referencia)
        /////////////////////////////////////////////////////////////////////////////////////////////////////
        if (EnableTest1 and numSemiciclosCarga == numCiclos2V) {
        
          derivadaminhistorica = 0.0;
  
          // Calculamos la media de los ciclos 3, 4 y 5
          // Empieza en 3, pues en el cero no se almacena nada
          for (int i=3; i<=numCiclos2V; i++){
            derivadaminhistorica = derivadaminhistorica + derivadasMinimasCarga[i];
            numelemmediaderref = numelemmediaderref + 1;
          }
          derivadaminhistorica = derivadaminhistorica / numelemmediaderref;
          numelemmediaderref = 0;
        }
        // Nos quedamos con la derivada del primer ciclo
        else if (EnableTest2 and numSemiciclosCarga == 1) {
          derivadaminhistorica = derivadasMinimasCarga[1];  
        }

        // Convertimos la derivada minima historica (referencia) en entero
        derivadaminhistorica100 = derivadaminhistorica*100.0;
        derivadaminhistoricaint = (long)derivadaminhistorica100;  

        // Debugueamos los valores
        Serial1.print(F("\n derivada min historica en float: "));
        Serial1.print(derivadaminhistorica);
        Serial1.print(F("\n derivada min historica x 100: "));
        Serial1.print(derivadaminhistorica100);
        Serial1.print(F("\n derivada min historica en valor entero: "));
        Serial1.print(derivadaminhistoricaint);
  
        // Convertimos la derivada minima actual en entero
        derivadaminactual = derivadasMinimasCarga[numSemiciclosCarga];
        derivadaminactual_100 = derivadaminactual*100.0;
        derivadaminactualint = (long)derivadaminactual_100;
        
        // Calculamos la diferencia entre la derivada minima actual y la de historica, EN FLOAT, pues con int daria 0
        diferenciaderivada =  derivadaminactual - derivadaminhistorica;
        
        // Sólo realizar division  si el cociente es diferente de cero (se mira en int, pues en float no hay precision)
        if (derivadaminhistoricaint != 0) {
          // La division hay que hacerla en float, ya que en int daría siempre 0
          divactualreferencia = diferenciaderivada / derivadaminhistorica;
          // Lo pasamos a entero
          divactualreferencia100 = divactualreferencia*100.0;
          divactualreferenciaint = (long)divactualreferencia100;         
        }
        else {
          divactualreferenciaint = 0;
          Serial1.println(F("\n la derivada historica es 0 "));
          Serial1.print(F("\n")); 
        }
         
        // debuguear valores
        Serial1.print(F("\n Nº semiciclos carga "));
        Serial1.print(numSemiciclosCarga);
        Serial1.print(F("\n derivada min actual: "));
        Serial1.print(derivadaminactual);
        Serial1.print(F("\n derivada min actual x 100: "));
        Serial1.print(derivadaminactual_100);
        Serial1.print(F("\n derivada min actual en valor entero: "));
        Serial1.print(derivadaminactualint);
        Serial1.print(F("\n diferencia derivada en float: "));
        Serial1.print(diferenciaderivada);
        Serial1.print(F("\n division derivada en float: "));
        Serial1.print(divactualreferencia);
        Serial1.print(F("\n division derivada x 100: "));
        Serial1.print(divactualreferencia100);
        Serial1.print(F("\n division derivada en entero, es decir, el porcentaje a comparar: "));
        Serial1.print(divactualreferenciaint);    
        Serial1.print(F("\n"));
  
        ///////////////////////////////////////////////////////////////
        //  Fin de DECISIÓN DE REBALANCEAR CON LA DERIVADA
        /////////////////////////////////////////////////////////////////////////////////////////////////////
        
        // Para mostrar info útil y para debugueo
        ImprimirInfoFinCarga();
        
        // Almacenamos la referencia de tiempos y cambiamos de estado
        epocaInicioDescarga = SegundosEjecucion;
          
        ecd = DESCARGA;  
      }// Fin de if (ADCOutputVoltageActual > valorcortefincarga){
      
      // Cambiamos de estado
      break;
      
    // Semiciclo de descarga
    case DESCARGA:

      // Reseteamos el flag
      fromChargeToDischarge = false;

      // Estamos en descarga
      SOCState = 2;

      // Reseteamos la derivada minima de la carga al maximo
      derivadaMin = 10000;
      
      // PASO DE DESCARGA A CARGA, en mV
      if (ADCOutputVoltageActual < 750.0){

        // Flag para señalizar otras partes del código
        fromDischargeToCharge = true;

        // Incrementamos el contador de semiciclos de descarga
        numSemiciclosDescarga = numSemiciclosDescarga + 1;
        
        // Almaceno el periodo anterior para compararlo más adelante
        periodoCicloDescargaPrevio = periodoCicloDescargaActual;
        
        // Almaceno el periodo actual
        periodoCicloDescargaActual = SegundosEjecucion - epocaInicioDescarga;
           
        // Para mostrar info útil y para debugueo
        ImprimirInfoFinDescarga();

        // Almacenamos la referencia de tiempos y cambiamos de estado
        epocaInicioCarga = SegundosEjecucion;

        // Como ha terminado el ciclo de descarga, incremetamos en uno el número de ciclos totales
        numCiclos++;

        // Cambiamos de estado
        ecd = CARGA;    
      }    
      break;

    // En cualquier otro caso
    default:
      Serial1.println("ERROR: estado no contemplado! ");
  }
}

// Imprimo la información del fin de carga, etnre ellas, la derivada mínima
void ImprimirInfoFinCarga() {
 
  // This is just for debugging purposes to test the code
  Serial1.print(F("\n"));
  Serial1.print(F("Acaba de finalizar un semiciclo de CARGA"));
  Serial1.print(F("\n"));

  Serial1.print(F("Periodo actual carga Ta: "));
  Serial1.print(periodoCicloCargaActual);
  Serial1.print(F("\n"));

  // Imprimir derivada mínima del actual ciclo de carga, y el vector con el array de los calculados, para ver la evolucion
  Serial1.print(F("Derivada minima del ciclo de carga: "));
  Serial1.print(derivadaMin);
  Serial1.print(F("\n"));

  Serial1.print(F("Array Derivada minima: "));
  Serial1.print(F("\n"));
  for (int i=1;i<=numSemiciclosCarga;i++){
      if (derivadasMinimasCarga[i] != 0){
        // Imprimimos 4 posiciones de decimal para mejorar debugueo
        Serial1.println(derivadasMinimasCarga[i],4);
      }
  }

  // Para debuguear lastBalChargeSemicycle
  Serial1.print(F("\n"));
  Serial1.println(F("Valor lastlastBalChargeSemicycle: "));
  Serial1.print(lastBalChargeSemicycle);
  Serial1.print(F("\n"));
  Serial1.print(F("\n"));
  Serial1.println(F("Numero Semiciclos carga finalizados: "));
  Serial1.print(numSemiciclosCarga);
  Serial1.print(F("\n"));
  
  Serial1.print(F("\n"));
  Serial1.println(F("Comienza un ciclo de DESCARGA"));
  Serial1.print(F("\n"));
  
  Serial1.print(F("Cantidad de RAM libre: "));
  Serial1.print(freeMemory());
  Serial1.print(F("\n"));
        
}

// Para debuguear, temporal pues luego el vuelco de ficheros no va bien
void ImprimirInfoFinDescarga() {
  
  // This is just for debugging purposes to test the code
  Serial1.print(F("\n"));
  Serial1.print(F("Acaba de finalizar un semiciclo de DESCARGA"));
  Serial1.print(F("\n"));

  Serial1.print(F("Periodo actual descarga Ta: "));
  Serial1.print(periodoCicloDescargaActual);
  
  Serial1.print(F("\n"));
  Serial1.print(F("Numero Semiciclos descarga finalizados: "));
  Serial1.print(numSemiciclosDescarga);
  Serial1.print(F("\n"));

  Serial1.print(F("\n"));
  Serial1.println(F("Comienza un ciclo de CARGA"));
  Serial1.print(F("\n"));
        
}

void setADS() {

  //Inicializamos el ADC ADS1115 para poder trabajar con él
  ads1115_Bateria.begin();

  //Default ADC ADS1115 I2C address is 0x48. To change it for example to 0x49, use "ads1115.begin(0x49);"
   
  //Si ha habido algún problema en la inicalización, mostrar un mensaje en el serial plotter y congelar ejecución indefinidamente
  if (!ads1115_Bateria.begin()) {
    Serial1.println ("Error al inicializar el ADC");
    while (1);
  }

  //Establecemos la ganancia PGA del ADS, nos interesa un PGA de 1 (que equivale a un factor de escala de 0.0001250 y a una referencia de 4,096V)
  ads1115_Bateria.setGain(GAIN_ONE);

  //Establecemos la ganancia PGA del ADS, nos interesa un PGA de 2 (que equivale a un factor de escala de 0.0000625 y a una referencia de 2,048V)
  //ads1115_Bateria.setGain(GAIN_TWO);
  
  // Data rate de 8 sps (lo mas lento posible). Valores a poner, aquí https://github.com/RobTillaart/ADS1X15
  ads1115_Bateria.setDataRate(0);
}

void leerModoDebug() {
  ;  
}

void mostrarTiempoEjecucion() {

  segundos = segundos + 2;

  if (segundos == 60) {
    segundos = 0;
    minutos = minutos + 1;
  }

  if (minutos == 60) {
    minutos = 0;
    horas = horas + 1;
  }

  if (horas == 24) {
    horas = 0;
    dias = dias + 1;
  }
  
}

void setup() {

  //Configuramos el pin correspondiente para el balanceador en la placa arduino como salida
  pinMode(SALIDA_BALANCEADOR,OUTPUT);
  
  //Iniciamos la comunicación con el puerto serie USB de este PC para enviar los datos por el serial plotter de Arduino IDE
  Serial.begin (SERIALSPEED);

  //10/05/2024
  Serial1.begin(SERIALSPEED);

  // Configuramos el ADS1115
  setADS();

  // Seleccionamos el test a lanzar, sólo uno cada vez.
  // Test #1
  EnableTest1 = false;
  numCiclos2V = 5; // Para saber cuándo corto a 1,6V o a 2V
  // Test #2
  EnableTest2 = true;

  // Para seleccionar si queremos debuguear o no
  //modoDebug = false;

}

void loop() {

  // Guardo referencia de tiempo para usar en descarte de transiciones
  currentMillis = millis(); // para el rebalanceador NO BORRAR
  tiempoactual = millis();  // para otras variables NO BORRAR
  SegundosEjecucion = millis()/1000; // para otras NO BORRAR

  //Importante: no guardar valor en una float pues el atmel 2560 es de 8 bits
  salidaADC = ads1115_Bateria.readADC_Differential_0_1();

  //valor final en milivoltios
  ADCOutputVoltageActual = multiplier * salidaADC;

  // Sólo realizaré acciones cada cierto tiempo, normalmente cada 2 segundos
  if (tiempoactual - tiempopreviomuestreo >= TIEMPOMUESTREOMSEG){

    // Almaceno el valor actual para no volver a entrar
    tiempopreviomuestreo = tiempoactual;

    // Para debuguear el valor de segundos ejecucion
    //Serial1.println("Tiempo en segundos: ");
    //Serial1.println(SegundosEjecucion);
    //Serial1.println("Tiempo en milisegundos: ");
    //Serial1.println(tiempoactual);

    // 28/02/2024 -> imprimo lo indispensable y separado por comas en lugar de por espacios
    // Arduino no soporta float en sprintf, asi que convertir los float a parte entera + parte decimal
    dtostrf( ADCOutputVoltageActual, 4, 2, szF1 );
    dtostrf( derivadaMin, 8, 2, szF2 );
    retmuestras = sprintf(muestras, "D: %d H: %d M: %d S: %d,%d,%d,%s,%d,%d,%d,%d,%s",
                                    dias,horas,minutos,segundos,numCiclos,SOCState,szF1,EstadoBalanceador,estadoBal,fromDischargeToCharge,fromChargeToDischarge,szF2);
  
    // This is just for debugging purposes to test the code
    if (retmuestras < 0) {
      Serial1.println(F("No byte written"));
      } 
    else if (retmuestras >= NUMCHARMUESTRAS) {
      Serial1.println(F("Too many bytes writen"));
    } else {
      // ok
      Serial1.print(F("\n"));
      Serial1.print(muestras);
    }

    MediaVoltajeyDerivada();

    DerivadaMedia();

    DescartarTransicionesSOC();

    MaquinaEstadosCD();

    mostrarTiempoEjecucion();

  }

  //leerModoDebug();

  // El balanceador ha de llamarse en el loop principal pues ha de activarse/desactivarse en instantes diferentes al fin de un ciclo de carga
  Balanceador();

  
}
