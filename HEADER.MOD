const
    ALNG =  10;      (* NO. OF SIGNIFICANT CHARS IN IDENTIFIERS *)
    AMAX =  30;      (* SIZE OF array-TABLE   *)
    BMAX =  20;      (* SIZE OF BLOCK-TABLE   *)
    C2MAX = 20;      (* SIZE OF REAL CONSTANT TABLE      *)
    CSMAX = 30;      (* MAX NO. OF CASES      *)
    CMAX = 600;      (* SIZE OF CODE          *)
    ERMAX = 59;      (* MAX ERROR NO.         *)
    EMAX  = 77;      (* MAX EXPONENT of REAL NUMBERS     *)
    EMIN = -78;      (* MIN EXPONENT          *)
    HEADER = 'Co-Pascal    December 1985    MS-DOS  ver 2.0';
    KMAX = 7;        (* max No. of significant digits    *)
    LLNG = 83;       (* input line length     *)
    LINELENG = 132;  (* output line length    *)
    LINELIMIT = 200; (* max No. of run time output lines *)
    NKW = 29;        (* No. of key words      *)
    NMAX = MAXINT;   (* 2**16-1               *)
    LMAX = 7;        (* maximum level         *)
    ORDMINCHAR = 0;  (* ORD of first char     *)
    ORDMAXCHAR = 255;(* ORD of last char      *)
    OMAX =  63;      (* highest order code    *)
    SMAX = 400;      (* size of string-table  *)
    STMAX = 1100;
    STKINCR = 200;
    PMAX = 4;        (* max # of concurrent processes    *)
    TMAX = 100;      (* size of identifier table         *)
    XMAX = MAXINT;   (* 2**16-1                          *)

type INDEX  = -XMAX .. +XMAX;
     ALFA   = array[ 1..ALNG ] of char;
     FNAME  = string[10];  (* [8] name + [2] drive  *)
     OBJECT = ( KONSTANT, VARIABLE, TYPE1, PROZEDURE, FUNKTION    );
     TYPES  = ( NOTYP, INTS, REALS, BOOLS, CHARS, ARRAYS, RECORDS );
     CHTP   = ( LETTER, LOWCASE, NUMBER, SPECIAL, ILLEGAL         );
     ITEM   = record
                TYP: TYPES;
                REF: INDEX;
              end;
     ORDER  = record
                F: -OMAX..+OMAX;
                X: -LMAX..+LMAX;
                Y: -NMAX..+NMAX;
              end;

     TYPSET = SET of TYPES;

var  DATA,
     SOURCE    :       TEXT;
     SFILE,
     DFILE     :      FNAME;  (* source & data file DISK name            *)
     CH        :       CHAR;  (* previous  char read from source program *)
     STANTYPS  :     TYPSET;
     PROGNAME  :       ALFA;
     CmdLine   : string[30];  (* CP/M : absolute $80 *)
     SS        : array[1..25] of char;  (* used for P_CODE_IO *)
     m, n      :    integer;
     option    :       char;
     DEBUG     :    boolean;  (* run-time program info on/off flag  *)

(*
   ===============
   compiler tables  - (Global) used by INTERPRT and COMPILE
   ===============
*)

    TAB:     array [0 .. TMAX] of record    (* identifier table *)
               NAME  : ALFA;
               LINK  : INDEX;
               OBJ   : OBJECT;
               TYP   : TYPES;
               REF   : INDEX;
               NORMAL: BOOLEAN;
               LEV   : 0 .. LMAX;
               ADR   : INTEGER;
             end;

    ATAB:    array [1 .. AMAX] of record     (* array-table *)
               INXTYP, ELTYP: TYPES;
               ELREF, LOW, HIGH, ELSIZE, SIZE: INDEX;
             end;

    BTAB:    array [ 1..BMAX ] of record     (* block-table  *)
               LAST,
               LASTPAR,
               PSIZE,
               VSIZE :   INDEX;
             end;

    STAB   : array [ 0.. SMAX] of CHAR;  (* string table *)
    CODE   : array [ 0.. CMAX] of ORDER;
    RCONST : array [ 1..C2MAX] of  REAL;
    B      : integer;   (* ---> index to BTAB,   *)

    IFLAG,                (* INPUT  found in program head *)
    OFLAG,                (* OUTPUT found in program head *)
    DFLAG  : BOOLEAN;     (* DATA   found in program head *)
