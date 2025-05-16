      procedure IFSTATEMENT;
      var X: ITEM;
          LC1,LC2: integer;
      begin
        INSYMBOL;
        EXPRESSION(FSYS+[thenSY,DOSY], X);
        if NOT (X.TYP in [BOOLS,NOTYP]) then ERROR(17);
        LC1 := LC;
        EMIT(11);  { JMPC }
        if SY = thenSY then INSYMBOL else begin
          ERROR(52);
          if SY = DOSY then INSYMBOL;
        end;
        STATEMENT(FSYS+[elseSY]);
        if SY = elseSY then begin
          INSYMBOL;
          LC2 := LC;
          EMIT(10);
          CODE[LC1].Y := LC;
          STATEMENT(FSYS);
          CODE[LC2].Y := LC;
        end else CODE[LC1].Y := LC;
      end;  { IFSTATEMENT }

      procedure CASESTATEMENT;
      var X: ITEM;
          I,J,K,LC1: integer;
          CASETAB: array [1..CSMAX] of record
                     VAL,
                     LC  : INDEX
                   end;
          EXITTAB: array [1..CSMAX] of integer;

        procedure CASELABEL;
        var LAB: CONREC; K: integer;
        begin
          CONSTANT(FSYS+[COMMA,COLON], LAB);
          if LAB.TP <> X.TYP then ERROR(47) else
          if I = CSMAX then FATAL(6) else begin
            I := I+1;
            K := 0;
            CASETAB[I].VAL := LAB.I;
            CASETAB[I].LC := LC;
            repeat
              K := K+1
            until CASETAB[K].VAL = LAB.I;
            if K < I then ERROR(1);   (*MULTIPLE DEFINITION*)
          end;
        end; (*CASELABEL*)

        procedure ONECASE;
        begin if SY in CONSTBEGSYS then
          begin CASELABEL;
            while SY = COMMA do begin
              INSYMBOL;
              CASELABEL
            end;
            if SY = COLON then INSYMBOL else ERROR(5);
            STATEMENT([SEMICOLON,ENDSY]+FSYS);
            J := J + 1;
            EXITTAB[J] := LC; EMIT(10)
          end
        end (*ONECASE*) ;

      begin
        INSYMBOL;
        I := 0;
        J := 0;
        EXPRESSION(FSYS+[OFSY,COMMA,COLON], X);
        if NOT (X.TYP in [INTS,BOOLS,CHARS,NOTYP]) then ERROR(23);
        LC1 := LC; EMIT(12);  (*JMPX*)
        if SY = OFSY then INSYMBOL else ERROR(8);
        ONECASE;
        while SY = SEMICOLON do begin
          INSYMBOL;
          ONECASE
        end;
        CODE[LC1].Y := LC;
        for K := 1 TO I do begin
          EMIT1(13,CASETAB[K].VAL);
          EMIT1(13,CASETAB[K].LC)
        end;
        EMIT1(10,0);
        for K := 1 TO J do CODE[EXITTAB[K]].Y := LC;
        if SY = ENDSY then INSYMBOL else ERROR(57)
      end (*CASESTATEMENT*) ;

      procedure repeatSTATEMENT;
      var X: ITEM; LC1: integer;
      begin
        LC1 := LC;
        INSYMBOL; STATEMENT([SEMICOLON,UNTILSY]+FSYS);
        while SY in [SEMICOLON]+STATBEGSYS do begin
          if SY = SEMICOLON then INSYMBOL else ERROR(14);
          STATEMENT([SEMICOLON,UNTILSY]+FSYS)
        end;
        if SY = UNTILSY then begin
          INSYMBOL; EXPRESSION(FSYS, X);
          if NOT (X.TYP in [BOOLS,NOTYP]) then ERROR(17);
          EMIT1(11,LC1)
        end else ERROR(53)
      end (*repeatSTATEMENT*) ;

      procedure whileSTATEMENT;
      var X: ITEM; LC1,LC2: integer;
      begin
        INSYMBOL;
        LC1 := LC;
        EXPRESSION(FSYS+[DOSY], X);
        if NOT (X.TYP in [BOOLS,NOTYP]) then ERROR(17);
        LC2 := LC; EMIT(11);
        if SY = DOSY then INSYMBOL else ERROR(54);
        STATEMENT(FSYS);
        EMIT1(10,LC1);
        CODE[LC2].Y := LC
      end; (* WHILESTATEMENT *)

      procedure FORSTATEMENT;
      var CVT : TYPES;
          X   : ITEM;
          I,F,LC1,LC2 : integer;
      begin
        INSYMBOL;
        if SY = IDENT then begin
          I := LOC(ID);
          INSYMBOL;
          if I = 0 then CVT := INTS
            else if TAB[I].OBJ = VARIABLE then begin
              CVT := TAB[I].TYP;
              if NOT TAB[I].NORMAL then ERROR(37)
                else EMIT2(0, TAB[I].LEV, TAB[I].ADR);
              if NOT (CVT in [NOTYP,INTS,BOOLS,CHARS]) then ERROR(18)
            end else begin
              ERROR(37);
              CVT := INTS
            end
          end else SKIP([BECOMES,TOSY,DOWNTOSY,DOSY]+FSYS, 2);
          if SY = BECOMES then begin
            INSYMBOL;
            EXPRESSION([TOSY,DOWNTOSY,DOSY]+FSYS, X);
            if X.TYP <> CVT then ERROR(19);
          end else SKIP([TOSY,DOWNTOSY,DOSY]+FSYS, 51);
        F := 14;
        if SY in [TOSY, DOWNTOSY] then begin
          if SY = DOWNTOSY then F := 16;
          INSYMBOL;
          EXPRESSION([DOSY]+FSYS, X);
          if X.TYP <> CVT then ERROR(19)
        end else SKIP([DOSY]+FSYS, 55);
        LC1 := LC; EMIT(F);
        if SY = DOSY then INSYMBOL else ERROR(54);
        LC2 := LC;
        STATEMENT(FSYS);
        EMIT1(F+1,LC2);
        CODE[LC1].Y := LC
      end; (* FORSTATEMENT *)

      procedure STANDPROC( N : integer );
      var I,F : integer;
          X,Y : ITEM;
      begin
        case N of
   1,2: begin (* READ *)
          if NOT ifLAG then begin
            ERROR(59);
            IFLAG := TRUE;
          end;
          if SY = LPARENT then begin
            repeat
              INSYMBOL;
              if DFLAG AND ( SY <> IDENT ) then begin
                I := pos( ' ', ID );
                if copy( ID, 1, i-1 ) = copy( DFILE, 11-i, i-1 )
                  then INSYMBOL else ERROR(2);
              end;
              if SY <> IDENT then ERROR(2) else begin
                I := LOC(ID);
                INSYMBOL;
                if I <> 0 then if TAB[I].OBJ <> VARIABLE
                  then ERROR(37) else begin
                    X.TYP := TAB[I].TYP;
                    X.REF := TAB[I].REF;
                    if TAB[I].NORMAL then F := 0 else F := 1;
                    EMIT2(F, TAB[I].LEV, TAB[I].ADR);
                    if SY in [LBRACK,LPARENT,PERIOD] then
                      SELECTOR(FSYS+[COMMA,RPARENT], X);
                    if X.TYP in [INTS,REALS,CHARS,NOTYP] then
                      EMIT1(27,ORD(X.TYP)) else ERROR(41)
                end;
              end;
              TEST([COMMA,RPARENT], FSYS, 6);
            until SY <> COMMA;
            if SY = RPARENT then INSYMBOL else ERROR(4)
          end;
          if N = 2 then EMIT(62)
        end;

   3,4: begin { WRITE }
          if SY = LPARENT then begin
            repeat
              INSYMBOL;
              if SY = WORD then begin
                EMIT1(24,SLENG);
                EMIT1(28,INUM);
                INSYMBOL;
              end else begin
                EXPRESSION(FSYS+[COMMA,COLON,RPARENT], X);
                if NOT (X.TYP in STANTYPS) then ERROR(41);
                if SY = COLON then begin
                  INSYMBOL;
                  EXPRESSION(FSYS+[COMMA,COLON,RPARENT], Y);
                  if Y.TYP <> INTS then ERROR(43);
                  if SY = COLON then begin
                    if X.TYP <> REALS then ERROR(42);
                    INSYMBOL;
                    EXPRESSION(FSYS+[COMMA,RPARENT], Y);
                    if Y.TYP <> INTS then ERROR(43);
                    EMIT(37)
                  end else EMIT1(30, ORD(X.TYP))
                end
                else EMIT1(29, ORD(X.TYP))
              end
            until SY <> COMMA;
            if SY = RPARENT then INSYMBOL else ERROR(4)
          end;
          if N = 4 then EMIT(63)
        end;
    5,6:  { WAIT,SIGNAL }
      if SY <> LPARENT then ERROR(9) else begin
        INSYMBOL;
        if SY<>IDENT then ERROR(0) else begin
          I := LOC(ID);
          INSYMBOL;
          if I <> 0 then if TAB[I].OBJ <> VARIABLE then ERROR(37)
            else begin
              X.TYP:=TAB[I].TYP;
              X.REF:=TAB[I].REF;
              if TAB[I].NORMAL then F:=0 else F:=1;
              EMIT2(F,TAB[I].LEV,TAB[I].ADR);
              if SY in [LBRACK,LPARENT,PERIOD] then SELECTOR(FSYS+[RPARENT],X);
              if X.TYP=INTS then EMIT(N+1) else ERROR(43)
              end
            end;
            if SY=RPARENT then INSYMBOL else ERROR(4)
          end;
        end (* CASE *)
      end; (* STANDPROC *)

    begin (*STATEMENT*)
      if SY in STATBEGSYS+[IDENT] then
          case SY of
            IDENT:    begin
                        I := LOC(ID);
                        INSYMBOL;
                        if I <> 0 then case TAB[I].OBJ of

                          KONSTANT,
                          TYPE1    : ERROR(45);
                          VARIABLE : ASSIGNMENT(TAB[I].LEV, TAB[I].ADR);
                          PROZEDURE: if TAB[I].LEV <> 0 then CALL(FSYS, I)
                                       else STANDPROC(TAB[I].ADR);
                          FUNKTION : if TAB[I].REF = DISPLAY[LEVEL]
                                       then ASSIGNMENT(TAB[I].LEV+1, 0)
                                         else ERROR(45);
                        end; (* case *)
                      end;

            BEGINSY  :  if ID = 'COBEGIN   ' then begin
                          EMIT(4);
                          COMPOUNDSTMNT;
                          EMIT(5)
                        end else COMPOUNDSTMNT;

            IFSY     :     IFSTATEMENT;
            CASESY   :   CASESTATEMENT;
            WHILESY  :  WHILESTATEMENT;
            REPEATSY : REPEATSTATEMENT;
            FORSY    :    FORSTATEMENT;
          end;
        TEST(FSYS, [], 14)
    end (*STATEMENT*) ;

begin (*BLOCK*)
  DX := 5;
  PRT := T;
  if LEVEL > LMAX then FATAL(5);
  TEST([LPARENT,COLON,SEMICOLON], FSYS, 14);
  ENTERBLOCK;
  DISPLAY[LEVEL] := B;
  PRB := B;
  TAB[PRT].TYP := NOTYP;
  TAB[PRT].REF := PRB;
  if ( SY = LPARENT ) AND ( LEVEL > 1 ) then PARAMETERLIST;
  BTAB[PRB].LASTPAR := T;
  BTAB[PRB].PSIZE := DX;
  if ISFUN then
    if SY = COLON then begin
      INSYMBOL;   (*FUNCTION TYPE*)
      if SY = IDENT then begin
        X := LOC(ID);
        INSYMBOL;
        if X <> 0 then
          if TAB[X].OBJ <> TYPE1 then ERROR(29) else
            if TAB[X].TYP in STANTYPS then TAB[PRT].TYP := TAB[X].TYP
              else ERROR(15)
      end else SKIP([SEMICOLON]+FSYS, 2)
    end else ERROR(5);
  if SY = SEMICOLON then INSYMBOL else ERROR(14);
  repeat
    if SY = CONSTSY then CONSTDECLARATION;
    if SY =  TYPESY then  TYPEDECLARATION;
    if SY =   VARSY then    VARDECLARTION;
    BTAB[PRB].VSIZE := DX;
    while SY in [PROCSY,FUNCSY] do PROCDECLARATION;
    TEST([BEGINSY], BLOCKBEGSYS+STATBEGSYS, 56)
  until SY in STATBEGSYS;
  TAB[PRT].ADR := LC;
  INSYMBOL;
  STATEMENT([SEMICOLON,ENDSY]+FSYS);
  while SY in [SEMICOLON]+STATBEGSYS do begin
    if SY = SEMICOLON then INSYMBOL else ERROR(14);
    STATEMENT([SEMICOLON,ENDSY]+FSYS)
  end;
  if SY = ENDSY then INSYMBOL else ERROR(57);
  TEST(FSYS+[PERIOD], [], 6)
end; { block }
