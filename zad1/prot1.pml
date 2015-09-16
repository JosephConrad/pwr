
/* 01 */ #define N	4                           /* liczba procesow */
/* 02 */ bool chce[N], we[N], wy[N];
/* 03 */ #define i _pid

         byte counter;

/* 04 */ active [N] proctype P()
/* 05 */ {
/* 06 */ start:
/* 07 */    chce[i] = true;

            int k;
         po_chce:
         przed_pocz: 
         k = 0;
            for (k : 0 .. N-1) {
                if 
                    :: !(chce[k] && we[k]) ->  skip
                    :: else -> goto przed_pocz;
                fi;
            }
           /*  czekaj, az dla wszystkich k z [0..N-1] zachodzi !(chce[k] && we[k]) */

/* 08 */    we[i] = true;
            
            do_poczekalnia:
            k = 0;
            for (k : 0 .. N-1) {
                if
                    :: (chce[k] && !we[k]) -> goto poczekalnia;
                    :: else -> skip;
                fi;
            }
            goto chce_wyjsc;

            /* jesli dla pewnego k z [0..N-1] zachodzi chce[k] && !we[k], to wykonaj 09..12, wpp. idź do 13 */

            poczekalnia:
/* 09 */    {    
/* 10 */        chce[i] = false;
                int j;
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
                goto po_poczekalni;
/* 12 */    }
            
/* 13 */    
            po_poczekalni:
            wy[i] = true;
            k = 0;
            for (k : i+1 .. N-1) {
                if 
                    :: (!we[k] || wy[k]) -> skip;
                    :: else -> goto po_poczekalni;
                fi;
            }
            /*  czekaj, az dla wszystkich k z [i+1..N-1] zachodzi !we[k] || wy[k] */
           
            do_sekcji:
            k = 0;
            for (k: 0 .. i -1){
                if 
                    :: (!we[k]) -> skip;
                    :: else -> goto do_sekcji;
                fi;
            }
            /*  czekaj, az dla wszystkich k z [0..i-1] zachodzi !we[k] */
            
            /* SEKCJA KRYTYCZNA */
            sk:
            counter++;
            counter--;
/* 14 */    
            wy[i] = false;
/* 15 */    we[i] = false;
/* 16 */    chce[i] = false;

/* 17 */    goto start
/* 18 */}

       // ltl sk { [] (counter < 2)}
       // ltl np { [] (P[i]@poczekalnia -> <> P[i]@sk) }
        //ltl test_war { [] (P[i]@po_poczekalni -> <>P[i]@sk) }
        ltl test_war { [] (P[i]@start -> <>P[i]@sk) }
       // ltl np { [] ! we[i]}
