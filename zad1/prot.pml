/* Konrad Lisiecki 291649 */
/* 01 */ #define N	4                           /* liczba procesow */
/* 02 */ bool chce[N], we[N], wy[N], nieunikniona_poczekalnia[N];
         int lin = 0;
/* 03 */ #define i _pid
         int poczatek[N];
         int licznik[N];

         byte counter;

/* 04 */ active [N] proctype P()
/* 05 */ {
/* 06 */ start:
            /*if 
                :: true -> true;
                :: true -> false;
            fi;*/
/* 07 */    chce[i] = true;

            /*********************************************************
            *  Liniowosc *
            *********************************************************/
            poczatek[i] = true;

            int k;
            przed_pocz: 
            /*  czekaj, az dla wszystkich k z [0..N-1] zachodzi !(chce[k] && we[k]) */
            k = 0;
            for (k : 0 .. N-1) {
                if 
                    :: !(chce[k] && we[k]) ->  skip;
                    :: else -> goto przed_pocz;
                fi;
            }

/* 08 */    we[i] = true;
            do_poczekalnia:
            /* jesli dla pewnego k z [0..N-1] zachodzi chce[k] && !we[k], to wykonaj 09..12, wpp. idź do 13 */
            k = 0;
            for (k : 0 .. N-1) {
                if
                    :: ((chce[k]) && !we[k]) -> goto poczekalnia;
                    :: else -> skip;
                fi;
            }
            goto po_poczekalni;

            poczekalnia:
/* 09 */    {    
                nieunikniona_poczekalnia[i] = true;
/* 10 */        chce[i] = false;
                czekaj:
                k = 0;
                for (k : 0 .. N-1) {
                    if 
                        :: (wy[k]) -> goto chce_wyjsc;
                        :: else -> skip;
                    fi;
                }
                goto czekaj;
                /*  czekaj, az dla pewnego k z [0..N-1] zachodzi wy[k] */
                chce_wyjsc:
/* 11 */        chce[i] = true;
/* 12 */    }
            
/* 13 */    
            po_poczekalni:
            wy[i] = true;
            tutaj:
            k = i+1;
            for (k : i+1 .. N-1) {
                if 
                    :: (!we[k] || wy[k]) -> skip;
                    :: else -> goto tutaj;
                fi;
            }
            /*  czekaj, az dla wszystkich k z [i+1..N-1] zachodzi !we[k] || wy[k] */
           
            do_sekcji:
            k = 0;
            for (k: 0 .. i-1){
                if 
                    :: (!we[k]) -> skip;
                    :: else -> goto do_sekcji;
                fi;
            }
            /*  czekaj, az dla wszystkich k z [0..i-1] zachodzi !we[k] */
            
            if
                :: i > 0 -> lin++;
                :: else -> skip;
            fi;

            
            /* SEKCJA KRYTYCZNA */
            sk:
            counter++;
            counter--;


            /*********************************************************
            *  Liniowosc *
            *********************************************************/
            k = 0;
            for (k: 0 .. N-1){
                if 
                    :: poczatek[k] -> licznik[k]++;
                    :: else -> skip;
                fi;
            } 

            poczatek[i] = false;
            licznik[i] = 0;
            /*********************************************************
            *  Liniowosc *
            *********************************************************/




            nieunikniona_poczekalnia[i] = false;
              /* 14 */     
            wy[i] = false;     
            /* 15 */    we[i] = false;
            /* 16 */    chce[i] = false; 
      


/* 17 */    goto start
/* 18 */}

//wzajemne wykluczanie // OK
ltl sk { [] (counter < 2)}

//nieunikniona poczekalnia: każde wejście do sekcji krytycznej procesu i poprzedzone jest przez stan o własności we[i] && !chce[i] 
//ltl np { [] (P[1]@sk -> nieunikniona_poczekalnia[1]) }

//wyjście z poczekalni: jeśli któryś z procesów i ma własność we[i] && !chce[i], to w końcu któryś z pozostałych procesów j będzie miał własność wy[j] 
//ltl wyj { [] (nieunikniona_poczekalnia[0] -> <>P[1]@tutaj || <>P[2]@tutaj || <>P[3]@tutaj)    }

//żywotność (brak zagłodzenia), nawet jeśli niektóre procesy utkną na zawsze we własnych sprawach
// Dla sprawdzenia tego warunku nalezy odkomentowac blok z ciaglym petleniem sie we wlasnych sprawach!!!
//ltl zyw { [] (P[i]@przed_pocz -> P[i]@sk) }

//liniowy czas oczekiwania: podczas gdy jakiś proces czeka, żaden inny proces nie może wejść do sekcji krytycznej więcej niż stałą liczbę razy 
//ltl lco {[](licznik[0] <= N) }