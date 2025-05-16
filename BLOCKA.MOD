procedure BLOCK( FSYS:SYMSET; ISFUN:boolean; LEVEL:integer );

type CONREC = record case TP: TYPES of
                INTS,CHARS,BOOLS: (I: INTEGER);
                REALS: (R: REAL)
              end;

var DX  : INTEGER;   (* data allocation index     *)
    PRT : INTEGER;   (* T-index of this procedure *)
    PRB : INTEGER;   (* B-index of this procedure *)
    X   : INTEGER;


procedure ENTERARRAY( TP: TYPES; L,H: INTEGER );
begin
  if L > H then ERROR(27);
  if ( ABS(L) > XMAX ) OR ( ABS(H) > XMAX ) then begin
    ERROR(27);
    L := 0;
    H := 0;
  end;
  if A = AMAX then FATAL(4) else begin
    A := A+1;
    with ATAB[A] do begin
      INXTYP := TP;
      LOW := L;
      HIGH := H
    end;
  end;
end; { ENTERARRAY }

procedure ENTERBLOCK;
begin
  if B = BMAX then FATAL(2) else begin
    B := B+1;
    BTAB[B].LAST := 0;
    BTAB[B].LASTPAR := 0;
  end;
end; { ENTERBLOCK }

procedure ENTERREAL(X: REAL);
begin
  if C2 = C2MAX-1 then FATAL(3) else begin
    RCONST[C2+1] := X;
    C1 := 1;
    while RCONST[C1] <> X do  C1 := C1+1;
    if C1 > C2 then C2 := C1
  end;
end; { ENTERREAL }

procedure SKIP( FSYS: SYMSET; N: INTEGER );
begin
  ERROR(N);
  SKIPFLAG := TRUE;
  while NOT ( SY IN FSYS ) do INSYMBOL;
  if SKIPFLAG then ENDSKIP;
end; { SKIP }

procedure TEST(S1,S2: SYMSET; N: INTEGER);
begin
  if NOT (SY IN S1) then SKIP(S1+S2,N);
end; { TEST }

procedure TESTSEMICOLON;
begin
  if SY = SEMICOLON then INSYMBOL else begin
    ERROR(14);
    if SY IN [COMMA,COLON] then INSYMBOL
  end;
  TEST([IDENT]+BLOCKBEGSYS, FSYS, 6)
end; { TESTSEMICOLON }

procedure ENTER( ID: ALFA; K: OBJECT );
var J,L: INTEGER;
begin
  if T = TMAX then FATAL(1) else begin
    TAB[0].NAME := ID;
    J := BTAB[DISPLAY[LEVEL]].LAST;
    L := J;
    while TAB[J].NAME <> ID do  J := TAB[J].LINK;
    if J <> 0 then ERROR(1) else begin
      T := T+1;
      with TAB[T] do begin
        NAME := ID;
        LINK := L;
        OBJ  := K;
        TYP  := NOTYP;
        REF  := 0;
        LEV  := LEVEL;
        ADR  := 0;
      end;
      BTAB[DISPLAY[LEVEL]].LAST := T;
    end;
  end;
end; { enter }

function LOC( ID: ALFA ): INTEGER;
var I,J: INTEGER;     (* locate identifier, ID, in table *)
begin
  I := LEVEL;
  TAB[0].NAME := ID;  (* sentinel *)
  repeat
    J := BTAB[DISPLAY[I]].LAST;
    while TAB[J].NAME <> ID do  J := TAB[J].LINK;
    I := I-1;
  until (I<0) OR (J<>0);
  if J = 0 then ERROR(0);
  LOC := J;
end; { LOC }

procedure ENTERVARIABLE;
begin
  if SY = IDENT then begin
    ENTER(ID,VARIABLE);
    INSYMBOL;
  end else ERROR(2);
end; { ENTERVARIABLE }

procedure CONSTANT(FSYS: SYMSET; var C: CONREC);
var X, SIGN: INTEGER;
begin
  C.TP := NOTYP;
  C.I  := 0;
  TEST(CONSTBEGSYS, FSYS, 50);
  if SY IN CONSTBEGSYS then begin
    if SY = CHARCON then begin
      C.TP := CHARS;
      C.I  := INUM;
      INSYMBOL;
    end else begin
      SIGN := 1;
      if SY IN [PLUS,MINUS] then begin
        if SY = MINUS then SIGN := -1;
        INSYMBOL;
      end;
      if SY = IDENT then begin
        X := LOC(ID);
        if X <> 0 then if TAB[X].OBJ <> KONSTANT then ERROR(25)
        else begin
          C.TP := TAB[X].TYP;
          if C.TP = REALS then C.R := SIGN*RCONST[TAB[X].ADR]
                          else C.I := SIGN*TAB[X].ADR
        end;
        INSYMBOL;
      end else if SY = INTCON then begin
        C.TP := INTS; C.I := SIGN*INUM;
        INSYMBOL
    end else if SY = REALCON then begin
      C.TP := REALS;
      C.R  := SIGN * RNUM;
      INSYMBOL;
      end else SKIP(FSYS,50);
    end;
    TEST(FSYS, [], 6);
  end;
end; { CONSTANT }

 procedure TYP( FSYS : SYMSET; var TP : TYPES; var RF, SZ : INTEGER);
 var X: INTEGER;
     ELTP: TYPES; ELRF: INTEGER;
     ELSZ, OFFSET, T0,T1: INTEGER;

   procedure ARRAYTYP(var AREF,ARSZ: INTEGER);
   var ELTP: TYPES;
       LOW, HIGH: CONREC;
       ELRF, ELSZ: INTEGER;
   begin
     CONSTANT([COLON,RBRACK,RPARENT,OFSY]+FSYS, LOW);
     if LOW.TP = REALS then begin
       ERROR(27);
       LOW.TP := INTS;
       LOW.I := 0;
     end;
     if SY = COLON then INSYMBOL else ERROR(13);
     CONSTANT([RBRACK,COMMA,RPARENT,OFSY]+FSYS, HIGH);
     if HIGH.TP <> LOW.TP then begin
       ERROR(27);
       HIGH.I := LOW.I;
     end;
     ENTERARRAY(LOW.TP, LOW.I, HIGH.I);
     AREF := A;
     if SY = COMMA then begin
       INSYMBOL;
       ELTP := ARRAYS;
       ARRAYTYP(ELRF,ELSZ)
     end else begin
       if SY = RBRACK then INSYMBOL else begin
         ERROR(12);
         if SY = RPARENT then INSYMBOL;
       end;
       if SY = OFSY then INSYMBOL else ERROR(8);
       TYP(FSYS,ELTP,ELRF,ELSZ);
     end;
     with ATAB[AREF] do begin
       ARSZ := (HIGH-LOW+1)*ELSZ;
       SIZE := ARSZ;
       ELTYP := ELTP;
       ELREF := ELRF;
       ELSIZE := ELSZ;
     end;
   end; { ARRAYTYP }

 begin { TYP }
   TP := NOTYP;
   RF := 0;
   SZ := 0;
   TEST(TYPEBEGSYS, FSYS, 10);
   if SY IN TYPEBEGSYS then begin
     if SY = IDENT then begin
       X := LOC(ID);
       if X <> 0 then with TAB[X] do
         if OBJ <> TYPE1 then ERROR(29) else begin
           TP := TYP;
           RF := REF;
           SZ := ADR;
           if TP = NOTYP then ERROR(30);
         end;
         INSYMBOL;
       end else
       if SY = ARRAYSY then begin
         INSYMBOL;
         if SY = LBRACK then INSYMBOL else begin
           ERROR(11);
           if SY = LPARENT then INSYMBOL
         end;
         TP := ARRAYS;
         ARRAYTYP(RF,SZ)
       end else begin { RECORDS }
         INSYMBOL;
         ENTERBLOCK;
         TP := RECORDS;
         RF := B;
         if LEVEL = LMAX then FATAL(5);
         LEVEL := LEVEL+1;
         DISPLAY[LEVEL] := B;
         OFFSET := 0;
         while NOT (SY IN FSYS-[SEMICOLON,COMMA,IDENT]+[ENDSY]) do begin
           if SY = IDENT then begin   (* field section *)
             T0 := T;
             ENTERVARIABLE;
             while SY = COMMA do begin
               INSYMBOL;
               ENTERVARIABLE
             end;
             if SY = COLON then INSYMBOL else ERROR(5);
             T1 := T;
             TYP(FSYS+[SEMICOLON,ENDSY,COMMA,IDENT],ELTP,ELRF,ELSZ);
             while T0 < T1 do begin
               T0 := T0+1;
               with TAB[T0] do begin
                 TYP    := ELTP;
                 REF    := ELRF;
                 NORMAL := TRUE;
                 ADR    := OFFSET;
                 OFFSET := OFFSET + ELSZ;
               end;
             end;
           end;
           if SY <> ENDSY then begin
             if SY = SEMICOLON then INSYMBOL else begin
               ERROR(14);
               if SY = COMMA then INSYMBOL;
             end;
             TEST([IDENT,ENDSY,SEMICOLON], FSYS, 6);
           end;
         end;
         BTAB[RF].VSIZE := OFFSET;
         SZ := OFFSET;
         BTAB[RF].PSIZE := 0;
         INSYMBOL;
         LEVEL := LEVEL-1;
       end;
       TEST(FSYS, [], 6);
     end;
   end; { TYP }

   procedure PARAMETERLIST;     (* formal parameter list *)
   var TP            :   TYPES;
       RF, SZ, X, T0 : INTEGER;
       VALPAR        : BOOLEAN;
   begin
     INSYMBOL;
     TP := NOTYP;
     RF := 0;
     SZ := 0;
     TEST([IDENT, VARSY], FSYS+[RPARENT], 7);
     while SY in [IDENT,VARSY] do begin
       if SY <> VARSY then VALPAR := TRUE else begin
         INSYMBOL;
         VALPAR := FALSE
       end;
       T0 := T;
       ENTERVARIABLE;
       while SY = COMMA do begin
         INSYMBOL;
         ENTERVARIABLE;
       end;
       if SY = COLON then begin
         INSYMBOL;
         if SY <> IDENT then ERROR(2) else begin
           X := LOC(ID);
           INSYMBOL;
           if X <> 0 then with TAB[X] do
             if OBJ <> TYPE1 then ERROR(29) else begin
               TP := TYP;
               RF := REF;
               if VALPAR then SZ := ADR else SZ := 1
             end;
           end;
           TEST([SEMICOLON,RPARENT], [COMMA,IDENT]+FSYS, 14)
         end else ERROR(5);
         while T0 < T do begin
           T0 := T0+1;
           with TAB[T0] do begin
             TYP := TP;
             REF := RF;
             NORMAL := VALPAR;
             ADR := DX;
             LEV := LEVEL;
             DX := DX + SZ
           end
         end;
         if SY <> RPARENT then begin
           if SY = SEMICOLON then INSYMBOL else begin
             ERROR(14);
             if SY = COMMA then INSYMBOL
           end;
           TEST([IDENT,VARSY], [RPARENT]+FSYS, 6)
         end
       end; { while }
     if SY = RPARENT then begin
       INSYMBOL;
       TEST( [ SEMICOLON, COLON ], FSYS, 6)
     end else ERROR(4)
   end; { PARAMETERLIST }

   procedure CONSTDECLARATION;
   var C: CONREC;
   begin
     INSYMBOL;
     TEST( [IDENT], BLOCKBEGSYS, 2);
     while SY = IDENT do begin
       ENTER( ID, KONSTANT );
       INSYMBOL;
       if SY = EQL then INSYMBOL else begin
         ERROR(16);
         if SY = BECOMES then INSYMBOL;
       end;
       CONSTANT( [SEMICOLON,COMMA,IDENT]+FSYS, C );
       TAB[T].TYP := C.TP;
       TAB[T].REF := 0;
       if C.TP = REALS then begin
         ENTERREAL( C.R );
         TAB[T].ADR := C1;
       end else TAB[T].ADR := C.I;
       TESTSEMICOLON;
     end;
   end; { CONSTDECLARATION }

   procedure TYPEDECLARATION;
   var TP        :   TYPES;
       RF, SZ, T1: INTEGER;
   begin
     INSYMBOL;
     TEST( [IDENT], BLOCKBEGSYS, 2);
     while SY = IDENT do begin
       ENTER( ID, TYPE1 );
       T1 := T;
       INSYMBOL;
       if SY = EQL then INSYMBOL else begin
         ERROR(16);
         if SY = BECOMES then INSYMBOL
       end;
       TYP([SEMICOLON,COMMA,IDENT]+FSYS, TP, RF, SZ);
       with TAB[T1] do begin
         TYP := TP;
         REF := RF;
         ADR := SZ
       end;
       TESTSEMICOLON;
     end;
   end; { TYPEDECLARATION }

   procedure VARDECLARTION;
   var T0, T1, RF, SZ : INTEGER;
       TP             :   TYPES;
   begin
     INSYMBOL;
     while SY = IDENT do begin
       T0 := T;
       ENTERVARIABLE;
       while SY = COMMA do begin
         INSYMBOL;
         ENTERVARIABLE;
       end;
       if SY = COLON then INSYMBOL else ERROR(5);
       T1 := T;
       TYP( [SEMICOLON,COMMA,IDENT]+FSYS, TP, RF, SZ );
       while T0 < T1 do begin
         T0 := T0+1;
         with TAB[T0] do begin
           TYP := TP;
           REF := RF;
           LEV := LEVEL;
           ADR := DX;
           NORMAL := TRUE;
           DX := DX + SZ;
         end;
       end;
       TESTSEMICOLON;
     end;
   end; { VARDECLARTION }

   procedure PROCDECLARATION;
   var ISFUN: BOOLEAN;
   begin
     ISFUN := ( SY = FUNCSY );
     INSYMBOL;
     if SY <> IDENT then begin
       ERROR(2);
       ID := '          '
     end;
     if ISFUN then ENTER( ID, FUNKTION ) else ENTER( ID, PROZEDURE );
     TAB[T].NORMAL := TRUE;
     INSYMBOL;
     block( [SEMICOLON]+FSYS, ISFUN, LEVEL+1 );
     if SY = SEMICOLON then INSYMBOL else ERROR(14 );
     EMIT(32+ORD(ISFUN))  { EXIT }
   end; { procedure DECLARATION }

(*---------------------------------------------------------STATEMENT--*)

   procedure STATEMENT( FSYS : SYMSET );
   var I : INTEGER;
       X : ITEM;
     procedure EXPRESSION( FSYS : SYMSET; var X: ITEM ); forward;

     procedure SELECTOR( FSYS: SYMSET; var V:ITEM );
     var X: ITEM; A,J: INTEGER;
     begin  (* SY IN [LPARENT, LBRACK, PERIOD] *)
       repeat
         if SY = PERIOD then begin
         INSYMBOL;        (* field selector *)
         if SY <> IDENT then ERROR(2) else begin
           if V.TYP <> RECORDS then ERROR(31)
           else begin (* search field identifier *)
             J := BTAB[V.REF].LAST;
             TAB[0].NAME := ID;
             while TAB[J].NAME <> ID do J := TAB[J].LINK;
             if J = 0 then ERROR(0);
             V.TYP := TAB[J].TYP;
             V.REF := TAB[J].REF;
             A := TAB[J].ADR;
             if A <> 0 then EMIT1(9,A);
           end;
           INSYMBOL;
         end;
       end else begin  (* array selector *)
         if SY <> LBRACK then ERROR(11);
         repeat
           INSYMBOL;
           EXPRESSION(FSYS+[COMMA,RBRACK], X);
           if V.TYP <> ARRAYS then ERROR(28) else begin
             A := V.REF;
             if ATAB[A].INXTYP <> X.TYP then ERROR(26)
               else if ATAB[A].ELSIZE = 1 then EMIT1(20,A) else EMIT1(21,A);
             V.TYP := ATAB[A].ELTYP;
             V.REF := ATAB[A].ELREF;
           end;
           until SY <> COMMA;
           if SY = RBRACK then INSYMBOL else begin
             ERROR(12);
             if SY = RPARENT then INSYMBOL
           end;
         end;
       until NOT ( SY IN [ LBRACK, LPARENT, PERIOD ] );
       TEST( FSYS, [], 6 );
     end; { SELECTOR }

     procedure CALL( FSYS: SYMSET; I: INTEGER );
     var X            : ITEM;
         LASTP, CP, K : INTEGER;
     begin
       EMIT1(18,I);  (* mark stack *)
       LASTP := BTAB[TAB[I].REF].LASTPAR;
       CP := I;
       if SY = LPARENT then begin (* actual parameter list *)
         repeat
           INSYMBOL;
           if CP >= LASTP then ERROR(39) else begin
             CP := CP+1;
             if TAB[CP].NORMAL then begin  (*  value parameter *)
               EXPRESSION( FSYS+[COMMA,COLON,RPARENT], X );
               if X.TYP=TAB[CP].TYP then begin
                 if X.REF <> TAB[CP].REF then ERROR(36)
                   else if X.TYP = ARRAYS then EMIT1(22,ATAB[X.REF].SIZE)
                     else if X.TYP = RECORDS
                       then EMIT1(22,BTAB[X.REF].VSIZE)
               end else if (X.TYP=INTS) AND (TAB[CP].TYP=REALS)
                 then EMIT1(26,0) else if X.TYP<>NOTYP then ERROR(36);
             end else begin  (* variable parameter *)
               if SY <> IDENT then ERROR(2) else begin
                 K := LOC(ID);
                 INSYMBOL;
                 if K <> 0 then begin
                   if TAB[K].OBJ <> VARIABLE then ERROR(37);
                   X.TYP := TAB[K].TYP;
                   X.REF := TAB[K].REF;
                   if TAB[K].NORMAL then EMIT2( 0,TAB[K].LEV, TAB[K].ADR )
                                    else EMIT2( 1,TAB[K].LEV, TAB[K].ADR );
                   if SY IN [ LBRACK, LPARENT, PERIOD ]
                     then SELECTOR(FSYS+[COMMA,COLON,RPARENT], X);
                   if ( X.TYP<>TAB[CP].TYP ) OR ( X.REF<>TAB[CP].REF )
                     then ERROR(36);
                 end;
               end;
             end;
           end;
           TEST( [COMMA,RPARENT], FSYS, 6 );
         until SY <> COMMA;
         if SY = RPARENT then INSYMBOL else ERROR(4);
       end;
       if CP < LASTP then ERROR(39); (* too few actual parameters *)
       EMIT1( 19, BTAB[TAB[I].REF].PSIZE-1 );
       if TAB[I].LEV < LEVEL then EMIT2( 3, TAB[I].LEV, LEVEL )
     end; { CALL }

     function RESULTTYPE( A,B : TYPES ): TYPES;
     begin
        if ( A > REALS ) OR ( B > REALS ) then begin
          ERROR(33);
          RESULTTYPE := NOTYP;
        end else if (A=NOTYP) OR (B=NOTYP) then RESULTTYPE := NOTYP
          else if A=INTS then if B=INTS then RESULTTYPE := INTS
            else begin
              RESULTTYPE := REALS;
              EMIT1(26,1);
            end else begin
              RESULTTYPE := REALS;
            if B=INTS then EMIT1(26,0)
          end;
      end; { RESULTTYPE }
