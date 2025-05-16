procedure INSYMBOL;     (* reads next symbol *)
label 1,2,3;
var I,J,K,E: integer;

  procedure READSCALE;
  var S, SIGN: integer;
  begin
    NEXTCH;
    SIGN := 1;
    S := 0;
    if CH = '+' then NEXTCH else
      if CH = '-' then begin
        NEXTCH;
        SIGN := -1;
      end;
    if NOT (CH IN ['0'..'9'])
      then ERROR(40)
      else repeat
        S := 10*S + ORD(CH) - ORD('0');
        NEXTCH;
      until NOT (CH IN ['0'..'9']);
      E := S*SIGN + E;
   end; { READSCALE }

   procedure ADJUSTSCALE;
   var S   : integer;
       D,T : real;
   begin
     if K+E > EMAX then ERROR(21)
      else if K+E < EMIN then RNUM := 0
        else begin
          S := ABS(E);
          T := 1.0;
          D := 10.0;
          repeat
            while NOT ODD(S) do begin
              S := S DIV 2;
              D := SQR(D);
            end;
            S := S-1;
            T := D*T;
          until S = 0;
          if E >= 0 then RNUM := RNUM*T
                    else RNUM := RNUM/T;
        end;
   end; { ADJUSTSCALE }

begin { INSYMBOL }
1: while CH = ' ' do NEXTCH;
   if CHARTP[CH] = ILLEGAL then begin
     NEXTCH;
     ERROR(24); writeln(' char is :: ', ORD(CH) );
     goto 1;
   end;
   case CH OF

   'A'..'Z',
   'a'..'z'  :    begin    (* identifier or wordsymbol *)
                    K  := 0;
                    ID := '          ';
                    repeat
                      if K < ALNG then begin
                         K := K+1;
                         ID[K] := UpCase( CH );
                      end;
                      NEXTCH;
                    until (CH <> '_') AND ( CHARTP[CH] in [SPECIAL,ILLEGAL]);
                    I := 1;
                    J := NKW;   (*BINARY SEARCH*)
                    repeat K := (I+J) DIV 2;
                      if ID <= KEY[K] then J := K-1;
                      if ID >= KEY[K] then I := K+1;
                    until I > J;
                    if I-1 > J then SY := KSY[K] else SY := IDENT;
                  end;

'0'..'9': begin { NUMBER }
            K := 0;
            INUM := 0;
            SY := INTCON;
            repeat
              INUM := INUM*10 + ORD(CH) - ORD('0');
              K := K+1;
              NEXTCH;
            until CHARTP[CH] <> NUMBER;
            if (K > KMAX) OR (INUM > NMAX) then begin
              ERROR(21);
              INUM := 0;
              K := 0;
            end;
            if CH = '.' then begin
              NEXTCH;
              if CH = '.' then CH := ':'
                else begin
                  SY := REALCON;
                  RNUM := INUM;
                  E := 0;
                  while CHARTP[CH] = NUMBER do begin
                    E := E-1;
                    RNUM := 10.0*RNUM + (ORD(CH)-ORD('0'));
                    NEXTCH
                 end;
                 if E = 0 then ERROR(40);
                 if CH = 'E' then READSCALE;
                 if E <> 0 then ADJUSTSCALE
               end;
             end else if CH = 'E' then begin
               SY := REALCON;
               RNUM := INUM;
               E := 0;
               READSCALE;
               if E <> 0 then ADJUSTSCALE;
             end;
           end;

':' : begin
        NEXTCH;
        if CH = '=' then begin
          SY := BECOMES;
          NEXTCH;
        end else SY := COLON;
      end;

'<' : begin
        NEXTCH;
        if CH = '=' then begin
          SY := LEQ;
          NEXTCH;
        end else if CH = '>' then begin
          SY := NEQ;
          NEXTCH;
        end else SY := LSS;
      end;

'>' : begin
        NEXTCH;
        if CH = '=' then begin
          SY := GEQ;
          NEXTCH;
        end else SY := GTR;
      end;

'.' : begin
        NEXTCH;
         if CH = '.' then begin
           SY := COLON;
           NEXTCH;
         end else SY := PERIOD;
      end;

'''': begin
        K := 0;
     2: NEXTCH;
        if CH = '''' then begin
          NEXTCH;
          if CH <> '''' then goto 3
        end;
        if SX+K = SMAX then FATAL(7);
        STAB[SX+K] := CH;
        K := K+1;
        if CC = 1 then K := 0   (*END OF LINE*)
                  else goto 2;
     3: if K = 1 then begin
          SY := CHARCON;
          INUM := ORD(STAB[SX]);
        end else
          if K = 0 then begin
            ERROR(38);
            SY   := CHARCON;
            INUM := 0;
          end else begin
            SY    := WORD;
            INUM  :=   SX;
            SLENG :=    K;
            SX    := SX+K;
          end;
      end;

'(' : begin
        NEXTCH;
        if CH <> '*' then SY := LPARENT
        else begin    (* comment *)
          NEXTCH;
          repeat
            while CH <> '*' do NEXTCH;
            NEXTCH
          until CH = ')';
          NEXTCH;
          goto 1;
        end
      end;

'{' : begin            (* comment *)
        while CH <> '}' do NEXTCH;
        NEXTCH;
        goto 1;
      end;

'+', '-', '*', '/', ')', '=', ',', '[', ']',  ';' :
      begin
        SY := SPS[CH];
        NEXTCH;
      end;

'$', '!', '@', '\', '^', '_', '?', '"', '&', '%' :
      begin
        ERROR(24);
        writeln(' [ $!@\^_?"&%  ]' );
        NEXTCH;
        goto 1;
      end;
   end;
end; { INSYMBOL }
