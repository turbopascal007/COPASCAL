
(*---------------------------------------------------EXPRESSION-----*)

      procedure EXPRESSION (* FSYS: SYMSET; var X: ITEM *) ;
      (*
         Note: dynamic variables for Y have been used due to the
               constraints imposed upon local variables in recursion.
      *)

      type ITEMptr = ^ITEM;   (* static > dynamic : SCHOENING *)
      var Y  : ITEMptr;
          OP : SYMBOL;

        procedure SIMPLEEXPRESSION( FSYS : SYMSET; var X : ITEM );
        var Y  : ITEMptr;
            OP : SYMBOL;

          procedure TERM( FSYS : SYMSET; var X : ITEM );
          var Y  : ITEMptr;
              OP : SYMBOL;
              TS : TYPSET;

            procedure FACTOR( FSYS : SYMSET; var X : ITEM );
            var I, F : INTEGER;

              procedure STANDFCT( N : INTEGER );
              var TS: TYPSET;
              begin (*STANDARD FUNCTION NO. N*)
                if SY = LPARENT then INSYMBOL else ERROR(9);
                if ( N < 17 ) OR ( N=19 ) then begin
                  EXPRESSION( FSYS+[RPARENT], X );
                  case N of

{ ABS, SQR }    0,2: begin
                       TS := [INTS,REALS];
                       TAB[I].TYP := X.TYP;
                       if X.TYP = REALS then N := N+1
                     end;

{ ODD, CHR    } 4,5: TS := [INTS];

{ ORD         } 6  : TS := [INTS,BOOLS,CHARS];

{ SUCC,  PRED } 7,8: begin
                       TS := [INTS,BOOLS,CHARS];
                       TAB[I].TYP := X.TYP
                     end;

{ ROUND,TRUNC } 9,10,11,12,13,14,15,16:
{ SIN,COS,... }      begin
                       TS := [INTS,REALS];
                       if X.TYP = INTS then EMIT1(26,0)
                     end;

{ RANDOM      } 19:  begin
                       TS := [INTS];
                       TAB[I].TYP := X.TYP;
                     end;
                  end; (* case *)
                  if X.TYP in TS then EMIT1(8,N) else
                  if X.TYP <> NOTYP then ERROR(48);

                end else begin (* N in [17,18] *)
{ EOF, EOLN   }   if SY <> IDENT then ERROR(2) else
                  if ID <> 'INPUT     ' then ERROR(0) else INSYMBOL;
                  EMIT1(8,N);
                end;
                X.TYP := TAB[I].TYP;
                if SY = RPARENT then INSYMBOL else ERROR(4)
              end; (* STANDFCT *)

            begin (* FACTOR *)
              X.TYP := NOTYP;
              X.REF := 0;
              TEST(FACBEGSYS, FSYS, 58);
              while SY in FACBEGSYS do begin
{   ID   }      if SY = IDENT then begin
                  I := LOC(ID);
                  INSYMBOL;
                  WITH TAB[I] do case OBJ of

              KONSTANT: begin
                          X.TYP := TYP;
                          X.REF := 0;
                          if X.TYP = REALS then EMIT1(25,ADR)
                            else EMIT1(24,ADR)
                        end;

              VARIABLE: begin
                          X.TYP := TYP;
                          X.REF := REF;
                          if SY in [LBRACK,LPARENT,PERIOD] then begin
                            if NORMAL then F := 0 else F := 1;
                              EMIT2(F, LEV, ADR);
                              SELECTOR(FSYS,X);
                              if X.TYP in STANTYPS then EMIT(34)
                            end else begin
                              if X.TYP in STANTYPS then
                                if NORMAL then F := 1 else F := 2
                              else
                                if NORMAL then F := 0 else F := 1;
                              EMIT2(F, LEV, ADR)
                            end;
                        end;

              TYPE1, PROZEDURE:    ERROR(44);

              FUNKTION : begin
                           X.TYP := TYP;
                           if LEV <> 0 then CALL(FSYS, I) else STANDFCT(ADR);
                         end

                    end (*CASE,WITH*)
                  end else
                  if SY in [CHARCON,INTCON,REALCON] then begin
                     if SY = REALCON then begin
                       X.TYP := REALS;
                       ENTERREAL(RNUM);
                       EMIT1(25, C1)
                     end else
                     begin
                       if SY = CHARCON then X.TYP := CHARS
                                       else X.TYP := INTS;
                       EMIT1(24, INUM)
                     end;
                     X.REF := 0; INSYMBOL
                   end else
{   (   }          if SY = LPARENT then begin
                     INSYMBOL;
                     EXPRESSION(FSYS+[RPARENT], X);
                     if SY = RPARENT then INSYMBOL else ERROR(4);
                   end else
{  NOT  }          if SY = NOTSY then
                   begin
                     INSYMBOL;
                     FACTOR(FSYS,X);
                     if X.TYP=BOOLS then EMIT(35) else
                       if X.TYP<>NOTYP then ERROR(32)
                   end;
                  TEST(FSYS, FACBEGSYS, 6)
                end (*while*)
            end; (*FACTOR*)

          begin (*TERM*)
            new( Y );
            FACTOR(FSYS+[TIMES,RDIV,IDIV,IMOD,ANDSY], X);
            while SY in [TIMES,RDIV,IDIV,IMOD,ANDSY] do begin
                OP := SY;
                INSYMBOL;
                FACTOR(FSYS+[TIMES,RDIV,IDIV,IMOD,ANDSY], Y^ );
{  *  }         if OP = TIMES then begin
                  X.TYP := RESULTTYPE(X.TYP, Y^.TYP);
                  case X.TYP of
                    NOTYP: ;
                    INTS : EMIT(57);
                    REALS: EMIT(60);
                  end
                end else
{  /  }         if OP = RDIV then begin
                  if X.TYP = INTS then begin
                    EMIT1(26,1);
                    X.TYP := REALS
                  end;
                  if Y^.TYP = INTS then begin
                    EMIT1(26,0);
                    Y^.TYP := REALS
                  end;
                  if (X.TYP=REALS) AND (Y^.TYP=REALS) then EMIT(61)
                    else begin
                      if (X.TYP<>NOTYP) AND (Y^.TYP<>NOTYP) then ERROR(33);
                      X.TYP := NOTYP
                    end
                end else
{ AND }         if OP = ANDSY then begin
                  if (X.TYP=BOOLS) AND (Y^.TYP=BOOLS) then EMIT(56)
                    else begin
                      if (X.TYP<>NOTYP) AND (Y^.TYP<>NOTYP) then ERROR(32);
                      X.TYP := NOTYP
                    end
                end else
{ DIV,MOD }     begin (*OP in [IDIV,IMOD]*)
                  if (X.TYP=INTS) AND (Y^.TYP=INTS) then
                    if OP=IDIV then EMIT(58) else EMIT(59)
                  else begin
                    if (X.TYP<>NOTYP) AND (Y^.TYP<>NOTYP) then ERROR(34);
                    X.TYP := NOTYP
                  end
                end
              end;
            dispose( Y );
          end (*TERM*) ;

        begin (*SIMPLEEXPRESSION*)
          new( Y );
{ +, - }  if SY in [PLUS,MINUS] then begin
            OP := SY;
            INSYMBOL;
            TERM(FSYS+[PLUS,MINUS], X);
            if X.TYP > REALS then ERROR(33)
              else if OP = MINUS then EMIT(36)
          end else TERM( FSYS+[ PLUS,MINUS,ORSY ], X );
          while SY in [PLUS,MINUS,ORSY] do begin
            OP := SY;
            INSYMBOL;
            TERM(FSYS+[PLUS,MINUS,ORSY], Y^);
{ OR   }    if OP = ORSY then begin
                 if (X.TYP=BOOLS) AND (Y^.TYP=BOOLS) then EMIT(51)
                   else begin
                     if (X.TYP<>NOTYP) AND (Y^.TYP<>NOTYP) then ERROR(32);
                     X.TYP := NOTYP
                   end
               end else begin
                 X.TYP := RESULTTYPE(X.TYP, Y^.TYP);
                 case X.TYP of
                   NOTYP: ;
                   INTS : if OP = PLUS then EMIT(52) else EMIT(53);
                   REALS: if OP = PLUS then EMIT(54) else EMIT(55);
                 end;
               end;
            end;
          dispose( Y );
        end; (* SIMPLEEXPRESSION *)

      begin (*EXPRESSION*)
        new( Y );
        SIMPLEEXPRESSION(FSYS+[EQL,NEQ,LSS,LEQ,GTR,GEQ], X);
        if SY in [EQL,NEQ,LSS,LEQ,GTR,GEQ] then begin
          OP := SY;
          INSYMBOL;
          SIMPLEEXPRESSION(FSYS, Y^ );
          if (X.TYP in [NOTYP,INTS,BOOLS,CHARS]) AND (X.TYP = Y^.TYP) then
            case OP of
              EQL : EMIT(45);
              NEQ : EMIT(46);
              LSS : EMIT(47);
              LEQ : EMIT(48);
              GTR : EMIT(49);
              GEQ : EMIT(50);
            end else begin
              if X.TYP = INTS then begin
                X.TYP := REALS;
                EMIT1(26,1)
              end else if Y^.TYP = INTS then begin
                Y^.TYP := REALS;
                EMIT1(26,0);
              end;
              if (X.TYP=REALS) AND (Y^.TYP=REALS) then case OP of
                EQL : EMIT(39);
                NEQ : EMIT(40);
                LSS : EMIT(41);
                LEQ : EMIT(42);
                GTR : EMIT(43);
                GEQ : EMIT(44);
              end else ERROR(35);
            end;
            X.TYP := BOOLS;
          end;
        dispose( Y );
      end (*EXPRESSION*) ;

      procedure ASSIGNMENT(LV,AD: INTEGER);
      var X,Y: ITEM; F: INTEGER;
      (* TAB[I].OBJ in [VARIABLE,PROZEDURE] *)
      begin
        X.TYP := TAB[I].TYP;
        X.REF := TAB[I].REF;
        if TAB[I].NORMAL then F := 0 else F := 1;
        EMIT2(F, LV, AD);
        if SY in [LBRACK,LPARENT,PERIOD] then SELECTOR([BECOMES,EQL]+FSYS, X);
        if SY = BECOMES then INSYMBOL else begin
          ERROR(51);
          if SY = EQL then INSYMBOL
        end;
        EXPRESSION(FSYS, Y);
        if X.TYP = Y.TYP then
          if X.TYP in STANTYPS then EMIT(38) else
          if X.REF <> Y.REF then ERROR(46) else
          if X.TYP = ARRAYS then EMIT1(23, ATAB[X.REF].SIZE)
                            else EMIT1(23, BTAB[X.REF].VSIZE)
        else
        if (X.TYP=REALS) AND (Y.TYP=INTS) then begin
          EMIT1(26,0); EMIT(38)
        end else
          if (X.TYP<>NOTYP) AND (Y.TYP<>NOTYP) then ERROR(46)
      end; { ASSIGNMENT }

      procedure COMPOUNDSTMNT;
      begin
        INSYMBOL;
        STATEMENT([SEMICOLON,endSY]+FSYS);
        while SY in [SEMICOLON]+STATBEGSYS do begin
          if SY = SEMICOLON then INSYMBOL else ERROR(14);
          STATEMENT([SEMICOLON,endSY]+FSYS)
        end;
        if SY = EndSy then InSymbol else ERROR(57)
      end; { CompuundStatement }
