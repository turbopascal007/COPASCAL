(*
    Interpret the code in P-CODE, also uses the tables TAB & BTAB
    and the variable S to simulate the run time stack.
*)

{ procedure INTERPRET;  (* global code, tab, btab *) }

label 97,98;        (* trap label *)
const STEPMAX = 8;
      TRU   =  1;
      FALS  =  0;
      CHARL =  0;
      CHARH = 63;

type PTYPE = 0..PMAX;

var  IR: ORDER;      (* instruction buffer *)
     PS: (RUN,FIN,CASCHK,DIVCHK,INXCHK,STKCHK,LINCHK,LNGCHK,REDCHK,DEADLOCK);
     LNCNT, OCNT, BLKCNT, CHRCNT: integer;     (*COUNTERS*)
     H1,H2,H3,H4: integer;
     FLD: array [1..4] of integer;     (* default field widths *)

     S: array [ 1..STMAX ] of record
          case DUM : TYPES of        (*   S[B+0] = FCT RESULT  *)
            INTS  : ( I : integer);  (*   S[B+1] = RETURN ADR  *)
            REALS : ( R :    REAL);  (*   S[B+2] = STATIC LINK *)
            BOOLS : ( B : boolean);  (*   S[B+3] = DYNAMIC LINK*)
            CHARS : ( C :    CHAR);  (*   S[B+4] = TABLE INDEX *)
          end;

     PTAB: array[PTYPE] of RECORD
             PC : integer;    (*PROGRAM COUNTER*)
             T  : integer;    (*TOP STACK INDEX*)
             B  : integer;    (*BASE INDEX*)
             DISPLAY   : array [1..LMAX] of integer;
             STACKSIZE : integer;
             SUSPEND   : integer;
             ACTIVE    : boolean
           end;
     NPR,
     CURPR:PTYPE;
     STEPCOUNT:integer;
     PFLAG:boolean;

procedure CHOOSEPROC;
var D:integer;
begin
  D := PMAX + 1;
  CURPR := (CURPR+TRUNC( RANDOM * PMAX )) MOD ( PMAX+1 );
  while ((NOT PTAB[CURPR].ACTIVE) OR (PTAB[CURPR].SUSPEND<>0)) AND (D >= 0)
   do begin
     D:= D-1;
     CURPR:= (CURPR+1) MOD (PMAX+1)
   end;
  if ( D < 0 ) then PS := DEADLOCK
    else STEPCOUNT := TRUNC( RANDOM * STEPMAX );
end;

function ITOB( I : integer ) : boolean;
begin
  if I=TRU then ITOB := TRUE else ITOB := FALSE;
end;

function BTOI( B : boolean ) : integer;
begin
  if B then BTOI := TRU else BTOI := FALS;
end;

begin { INTERPRET }
  if DFLAG then begin
    writeln(' DFILE : ',DFILE, length(DFILE):10, DFILE[8]:3 );
    assign( DATA, DFILE + '.DAT' );
    reset( DATA );
  end;
  S[1].I :=  0;
  S[2].I :=  0;
  S[3].I := -1;
  S[4].I := BTAB[1].LAST;
  with PTAB[0] do begin
    B := 0;
    SUSPEND:=0;
    DISPLAY[1] := 0;
    T := BTAB[2].VSIZE - 1;
    PC := TAB[S[4].I].ADR;
    ACTIVE := TRUE;
    STACKSIZE := STMAX - PMAX*STKINCR;
  end;
  for CURPR:=1 to PMAX do with PTAB[CURPR] do begin
    ACTIVE := FALSE;
    DISPLAY[1] := 0;
    PC := 0;
    SUSPEND := 0;
    B := PTAB[CURPR-1].STACKSIZE + 1;
    STACKSIZE := B + STKINCR - 1;
    T := B-1;
  end;
  NPR:=0;
  CURPR:=0;
  PFLAG:=FALSE;
  STEPCOUNT:=0;
  RANDOMIZE;  (* initialize TURBO random number generator *)
  PS := RUN;
  LNCNT  :=  0;
  OCNT   :=  0;
  CHRCNT :=  0;
  FLD[1] := 10;
  FLD[2] := 22;
  FLD[3] := 10;
  FLD[4] :=  1;

  repeat
    if PTAB[0].ACTIVE then CURPR:=0
      else if STEPCOUNT = 0 then begin
        CHOOSEPROC;
        if PS=DEADLOCK then GOTO 98
      end else STEPCOUNT:=STEPCOUNT - 1;
    with PTAB[CURPR] do begin
      IR := CODE[PC];
      PC := PC+1;
      OCNT := OCNT + 1;
    end;
    if PFLAG then begin
      if IR.F = 18 then NPR:=NPR+1;
      CURPR := NPR;
    end;
    with PTAB[CURPR] do

    case IR.F of

    0: begin { load address }
         T := T+1;
         if T > STACKSIZE then PS := STKCHK
           else S[T].I := DISPLAY[IR.X] + IR.Y;
       end;
    1: begin { load value   }
       T := T+1;
       if T > STACKSIZE then PS := STKCHK
         else S[T] := S[DISPLAY[IR.X] + IR.Y];
       end;
    2: begin { load indirect }
         T := T+1;
         if T > STACKSIZE then PS := STKCHK
           else S[T] := S[S[DISPLAY[IR.X] + IR.Y].I]
       end;
    3: begin { update display }
         H1 := IR.Y;
         H2 := IR.X;
         H3 := B;
         repeat
           DISPLAY[H1] := H3;
           H1 := H1-1;
           H3 := S[H3+2].I;
         until ( H1 = H2 );
       end;
    4: PFLAG := TRUE;  (* CObegin *)
    5: begin           (* COend   *)
         PFLAG:= FALSE;
         PTAB[0].ACTIVE:=FALSE
       end;
    6: begin     { wait }
         H1 := S[T].I;
         T  := T-1;
         if S[H1].I > 0 then S[H1].I:=S[H1].I - 1
           else begin
             SUSPEND   := H1;
             STEPCOUNT := 0;
           end;
       end;
    7: begin     { signal }
         H1:=S[T].I;
         T:=T-1;
         H2:= PMAX+1;
         H3:= TRUNC( RANDOM*H2 );
         while ( H2 >= 0 ) AND ( PTAB[H3].SUSPEND <> H1 ) do begin
           H3 := (H3+1) MOD (PMAX+1);
           H2 := H2-1;
         end;
         if ( H2 < 0 ) OR ( S[H1].I < 0 )
           then S[H1].I := S[H1].I+1
           else PTAB[H3].SUSPEND := 0;
       end;
    8: case IR.Y OF      { standard procedures }
         0: S[T].I := ABS(S[T].I);
         1: S[T].R := ABS(S[T].R);
         2: S[T].I := SQR(S[T].I);
         3: S[T].R := SQR(S[T].R);
         4: S[T].B := ODD(S[T].I);
         5: begin { S[T].C := CHR(S[T].I); }
              if (S[T].I < 0) OR (S[T].I > 63) then PS := INXCHK
            end;
         6: { S[T].I := ORD(S[T].C) };
         7: S[T].C := SUCC(S[T].C);
         8: S[T].C := PRED(S[T].C);
         9: S[T].I := ROUND(S[T].R);
        10: S[T].I := TRUNC(S[T].R);
        11: S[T].R := SIN(S[T].R);
        12: S[T].R := COS(S[T].R);
        13: S[T].R := EXP(S[T].R);
        14: S[T].R := LN(S[T].R);
        15: S[T].R := SQRT(S[T].R);
        16: S[T].R := ARCTAN(S[T].R);
        17: begin
              T := T+1;
              if T > STACKSIZE then PS := STKCHK else S[T].B := EOF( DATA );
            end;
        18: begin
              T := T+1;
              if T > STACKSIZE then PS := STKCHK else S[T].B := EOLN( DATA );
            end;
        19: S[T].I := RANDOM( S[T].I + 1 );
       end;
    9: S[T].I := S[T].I + IR.Y;   (* offset *)
   10: PC := IR.Y;                (* jump   *)
   11: begin                      (* conditional junp *)
         if NOT S[T].B then PC := IR.Y;
         T := T-1
       end;
   12: begin (* switch *)
         H1 := S[T].I;
         T  := T-1;
         H2 := IR.Y;
         H3 := 0;
         repeat
           if CODE[H2].F <> 13 then begin
             H3 := 1;
             PS := CASCHK;
           end else
           if CODE[H2].Y = H1 then begin
             H3 := 1;
             PC := CODE[H2+1].Y
           end else H2 := H2 + 2;
         until ( H3 <> 0 );
       end;
   14: begin (* for1UP *)
         H1 := S[T-1].I;
         if H1 <= S[T].I then S[S[T-2].I].I := H1
           else begin
             T  := T-3;
             PC := IR.Y;
          end;
        end;
   15: begin (* for2up *)
         H2 := S[T-2].I;
         H1 := S[H2].I + 1;
         if H1 <= S[T].I then begin
           S[H2].I := H1;
           PC := IR.Y
         end else T := T-3;
       end;
   16: begin (* for1down *)
         H1 := S[T-1].I;
         if H1 >= S[T].I then S[S[T-2].I].I := H1
           else begin
             PC := IR.Y;
             T := T-3;
           end;
       end;
   17: begin (* for2down *)
         H2 := S[T-2].I;
         H1 := S[H2].I - 1;
         if H1 >= S[T].I then begin
           S[H2].I := H1;
           PC := IR.Y;
         end else T := T-3;
       end;
   18: begin (* mark stack *)
         H1 := BTAB[TAB[IR.Y].REF].VSIZE;
         if T+H1 > STACKSIZE then PS := STKCHK
           else begin
             T := T+5;
             S[T-1].I := H1-1;
             S[T].I := IR.Y;
           end;
       end;
   19: begin (* call *)
         ACTIVE := TRUE;
         H1 := T - IR.Y;
         H2 := S[H1+4].I;    (* H2 points to TAB *)
         H3 := TAB[H2].LEV;
         DISPLAY[H3+1] := H1;
         H4 := S[H1+3].I + H1;
         S[H1+1].I := PC;
         S[H1+2].I := DISPLAY[H3];
         S[H1+3].I := B;
         if PFLAG then S[H1+3].I:=PTAB[0].B
           else S[H1+3].I:=B;
         for H3 := T+1 to H4 do S[H3].I := 0;
         B := H1;
         T := H4;
         PC := TAB[H2].ADR;
       end;
   20: begin { INDEX1 }
         H1 := IR.Y;     (* H1 points to ATAB *)
         H2 := ATAB[H1].LOW;
         H3 := S[T].I;
         if H3 < H2 then PS := INXCHK
          else if H3 > ATAB[H1].HIGH then PS := INXCHK
            else begin
              T := T-1;
              S[T].I := S[T].I + (H3-H2);
            end;
       end;
   21: begin { INDEX }
         H1 := IR.Y;      (* H1 POINTS TO ATAB *)
         H2 := ATAB[H1].LOW; H3 := S[T].I;
         if H3 < H2 then PS := INXCHK else
         if H3 > ATAB[H1].HIGH then PS := INXCHK
           else begin
             T := T-1;
             S[T].I := S[T].I + (H3-H2)*ATAB[H1].ELSIZE;
           end;
       end;
   22: begin { load block }
         H1 := S[T].I; T := T-1;
         H2 := IR.Y + T; if H2 > STACKSIZE then PS := STKCHK else
         while T < H2 do begin
           T := T+1;
           S[T] := S[H1];
           H1 := H1+1;
         end
       end;
   23: begin { copy block }
         H1 := S[T-1].I;
         H2 := S[T].I; H3 := H1 + IR.Y;
         while H1 < H3 do begin
           S[H1] := S[H2];
           H1 := H1+1;
           H2 := H2+1;
         end;
         T := T-2;
       end;
   24: begin { literal }
         T := T+1;
         if T > STACKSIZE then PS := STKCHK else S[T].I := IR.Y;
       end;
   25: begin { load real }
         T := T+1;
         if T > STACKSIZE then PS := STKCHK else S[T].R := RCONST[IR.Y];
       end;
 26: begin (* FLOAT *)
       H1 := T - IR.Y;
       S[H1].R := S[H1].I;
     end;
 27: begin (* READ *)
       if EOF( DATA ) then PS := REDCHK else
         case IR.Y OF
           1 : READ( S[S[T].I].I );
           2 : READ( S[S[T].I].R );
           3 : begin
                 READ( CH );
                 S[S[T].I].I := ORD( CH );
               end;
           4 : READ(S[S[T].I].C);
         end;
       T := T-1;
     end;
 28: begin (* write STRING *)
       H1 := S[T].I; H2 := IR.Y; T := T-1;
       CHRCNT := CHRCNT+H1; if CHRCNT > LINELENG then PS := LNGCHK;
       repeat
         write(STAB[H2]);
         H1 := H1-1;
         H2 := H2+1
       until H1 = 0;
     end;
 29: begin (* write1 *)
       CHRCNT := CHRCNT + FLD[IR.Y];
       if CHRCNT > LINELENG then PS := LNGCHK else
       case IR.Y OF
        1: write(S[T].I: FLD[1]);
        2: write(S[T].R: FLD[2]);
        3: write(S[T].B: FLD[3]);
        4: write(S[T].C);            (*BURD*)
       end;
       T := T-1
     end;
 30: begin (* write2 *)
       CHRCNT := CHRCNT + S[T].I;
       if CHRCNT > LINELENG then PS := LNGCHK else
       case IR.Y OF
        1: write(S[T-1].I: S[T].I);
        2: write(S[T-1].R: S[T].I);
        3: write(S[T-1].B: S[T].I);
        4: write(S[T].C);            (*BURD*)
       end;
       T := T-2
     end;
 31: PS := FIN;
 32: begin (* EXIT procedure *)      (*BURD*)
       T := B-1;
       PC := S[B+1].I;
       if PC<>0 then B:= S[B+3].I
         else begin
           NPR := NPR-1;
           ACTIVE := FALSE;
           STEPCOUNT:=0;
           PTAB[0].ACTIVE:=(NPR=0)
         end;
     end;
 33: begin (* EXIT function *)
       T := B;
       PC := S[B+1].I;
       B := S[B+3].I;
     end;
 34: S[T] := S[S[T].I];
 35: S[T].B := NOT S[T].B;
 36: S[T].I := - S[T].I;
 37: begin
       CHRCNT := CHRCNT + S[T-1].I;
       if CHRCNT > LINELENG then PS := LNGCHK
         else write(S[T-2].R: S[T-1].I: S[T].I);
       T := T-3;
     end;
 38: begin (*STORE*)
       S[S[T-1].I] := S[T];
       T := T-2;
     end;
 39..61 : begin
            T := T-1;
            case IR.F of

             39 : S[T].B := ( S[T].R =  S[T+1].R );
             40 : S[T].B := ( S[T].R <> S[T+1].R );
             41 : S[T].B := ( S[T].R <  S[T+1].R );
             42 : S[T].B := ( S[T].R <= S[T+1].R );
             43 : S[T].B := ( S[T].R >  S[T+1].R );
             44 : S[T].B := ( S[T].R >= S[T+1].R );
             45 : S[T].B := ( S[T].I =  S[T+1].I );
             46 : S[T].B := ( S[T].I <> S[T+1].I );
             47 : S[T].B := ( S[T].I <  S[T+1].I );
             48 : S[T].B := ( S[T].I <= S[T+1].I );
             49 : S[T].B := ( S[T].I >  S[T+1].I );
             50 : S[T].B := ( S[T].I >= S[T+1].I );
             51 : S[T].B := ( S[T].B OR S[T+1].B );
             52 : S[T].I := S[T].I + S[T+1].I;
             53 : S[T].I := S[T].I - S[T+1].I;
             54 : S[T].R := S[T].R + S[T+1].R;
             55 : S[T].R := S[T].R - S[T+1].R;
             56 : S[T].B := ( S[T].B AND S[T+1].B );
             57 : S[T].I := S[T].I * S[T+1].I;
             58 : if S[T+1].I = 0 then PS := DIVCHK
                    else S[T].I := S[T].I DIV S[T+1].I;
             59 : if S[T+1].I = 0 then PS := DIVCHK
                    else S[T].I := S[T].I MOD S[T+1].I;
             60 : S[T].R := S[T].R * S[T+1].R;
             61 : S[T].R := S[T].R / S[T+1].R;
          end;  { case }
        end;  { begin }

62: if EOF( DATA ) then PS := REDCHK else READLN;
 63: begin
       writeln;
       LNCNT := LNCNT + 1;
       CHRCNT := 0;
       if LNCNT > LINELIMIT then PS := LINCHK;
     end
   end (*case*) ;
 until PS <> RUN;

98: if PS <> FIN then begin (* fatal error in user's program *)
      writeln;
      with PTAB[CURPR]
        do write(' HALT at',PC:5,'in process',CURPR:4,' because of ');
      case PS OF
        DEADLOCK: writeln( 'DEADLOCK'             );
        RUN     : writeln( 'ERROR (SEE DAYFILE)'  );
        CASCHK  : writeln( 'UNDEFINED CASE'       );
        DIVCHK  : writeln( 'DIVIDE BY 0'          );
        INXCHK  : writeln( 'INVALID INDEX'        );
        STKCHK  : writeln( 'STORAGE OVERFLOW'     );
        LINCHK  : writeln( 'TOO MUCH OUTPUT'      );
        LNGCHK  : writeln( 'LINE TOO LONG'        );
        REDCHK  : writeln( 'READ PAST END OF FILE');
      end;
      writeln('0PROCESS  ACTIVE  SUSPEND PC');
      for H1:=0 to PMAX do with PTAB[H1] do
        writeln('0',H1:4,'      ',ACTIVE,SUSPend:5,PC:8);
      writeln('0GLOBAL VARIABLES');
      for H1:= BTAB[1].LAST+1 to TMAX do
        with TAB[H1] do if LEV<>1 then GOTO 97
          else if OBJ=VARIABLE then if TYP IN STANTYPS then
        case TYP OF
          INTS  : writeln( NAME, ' = ', S[ADR].I );
          BOOLS : writeln( NAME, ' = ', S[ADR].B );
          CHARS : writeln( NAME, ' = ', CHR( S[ADR].I MOD 64 ));
          REALS : writeln( NAME, ' = ', S[ADR].R );
        end;
  97: writeln;
H1 := B;        (* post mortem dump *)
BLKCNT := 10;
    repeat
      writeln;
      BLKCNT := BLKCNT - 1;
      if BLKCNT = 0 then H1 := 0; H2 := S[H1+4].I;
      if H1<>0 then
        writeln(' ', TAB[H2].NAME, ' CALLED AT', S[H1+1].I: 5);
      H2 := BTAB[ TAB[H2].REF ].LAST;
      while H2 <> 0 do
      with TAB[H2] do begin
        if OBJ = VARIABLE then
          if TYP IN STANTYPS then begin
            write('    ', NAME, ' = ');
            if NORMAL then H3 := H1+ADR else H3 := S[H1+ADR].I;
            case TYP OF
              INTS:  writeln(S[H3].I);
              REALS: writeln(S[H3].R);
              BOOLS: writeln(S[H3].B);
              CHARS: writeln(CHR(S[H3].I MOD 64));
            end;
          end;
          H2 := LINK;
      end;
      H1 := S[H1+3].I;
    until ( H1 < 0 );
  end;
  if DEBUG then begin
    writeln;
    writeln( OCNT, ' STEPS' );
  end;
