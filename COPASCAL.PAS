(*

                  The  * Co-Pascal *  COMPILER

   ...is a modified version of the PASCAL-S compiler to permit
   interleaved concurrent program execution.  The reserved words
   "COBEGIN" and "COEND" mark concurrent blocks while calls to
   the predefined functions WAIT and SIGNAL provide synchronization.
   The changes are from "Principles of Concurrent Programming by
   BEN-ARI.

   The defining document for PASCAL-S is:

     PASCAL-S: A SUBSET AND ITS IMPLEMENTATION by N. WIRTH.


   HISTORY:

   .  PASCAL-S developed by N. Wirth,  1976.

   .  PASCAL-S modified for the HP/3000 by D. Greer.

   .  M. Ben-Ari develops additions to the Pascal language to provide
      for simulated concurrency.  See Ben-Ari : 'Principles of Concurrent
      Programming.  Pretice-Hall, 1982.

   .  B. Burd incorporates Ben-Ari's changes into PASCAL-S,
      developing CO-PASCAL for the VAX/11-750 under VMS, 1985.

   .  C. Schoening modifies and enhances CO-PASCAL for Turbo-Pascal v2.0
      under CP/M and MS-DOS, 1985.


*)


program Co_Pascal( INPUT, OUTPUT );

{$R+}
{$I HEADER.MOD }

(*------------------------------------------------------COMPILE-----*)

overlay procedure compile;

const KEY : array[1..NKW] of string[10] =
          ( 'AND       ', 'ARRAY     ',
            'BEGIN     ', 'CASE      ',
            'COBEGIN   ', 'COEND     ',
            'CONST     ', 'DIV       ',
            'DO        ', 'DOWNTO    ',
            'ELSE      ', 'END       ',
            'FOR       ', 'FUNCTION  ',
            'IF        ', 'MOD       ',
            'NOT       ', 'OF        ',
            'OR        ', 'PROCEDURE ',
            'PROGRAM   ', 'RECORD    ',
            'REPEAT    ', 'THEN      ',
            'TO        ', 'TYPE      ',
            'UNTIL     ', 'VAR       ',
            'WHILE     ' );


type  SYMBOL = ( INTCON, REALCON, CHARCON, WORD,
                 PLUS, MINUS, TIMES, IDIV, RDIV, IMOD,
                 NOTSY, ANDSY, ORSY,
                 EQL, NEQ, GTR, GEQ, LSS, LEQ,
                 LPARENT, RPARENT, LBRACK, RBRACK,
                 COMMA, SEMICOLON, PERIOD, COLON,
                 BECOMES, CONSTSY, TYPESY, VARSY, ARRAYSY, RECORDSY,
                 FUNCSY, PROCSY, PROGRAMSY, IDENT, BEGINSY, ENDSY,
                 REPEATSY, UNTILSY, WHILESY, DOSY, FORSY,
                 IFSY, THENSY, ELSESY, CASESY, OFSY, TOSY, DOWNTOSY );

      SYMSET = SET OF SYMBOL;

const KSY : array[1..NKW] of SYMBOL =
            ( ANDSY,        ARRAYSY,       BEGINSY,       CASESY,
              BEGINSY,      ENDSY,         CONSTSY,       IDIV,
              DOSY,         DOWNTOSY,      ELSESY,        ENDSY,
              FORSY,        FUNCSY,        IFSY,          IMOD,
              NOTSY,        OFSY,          ORSY,          PROCSY,
              PROGRAMSY,    RECORDSY,      REPEATSY,      THENSY,
              TOSY,         TYPESY,        UNTILSY,       VARSY,
              WHILESY );

var   DISPLAY : ARRAY [ 0 .. LMAX ] of INTEGER;
      SPS     : ARRAY [ ' '.. ']' ] of SYMBOL;

(*
   =============================
   key words and special symbols
   =============================
*)

   (* indicies to tables  *)

    T,   (* ---> TAB,    *)
    A,   (* ---> ATAB,   *)
    SX,  (* ---> STAB,   *)
    C1,  (* ---> RCONST, *)
    C2,  (* ---> RCONST  *)

    LC   (* program Location Counter *) : INTEGER;

(*
      =========================
       Error Control Variables
      =========================
*)

    ERRS     : SET OF 0..ERMAX;  (* compilation errors        *)
    ERRPOS   : INTEGER;
    SKIPFLAG : BOOLEAN;          (* used by procedure ENDSKIP *)

(*
      =============================
      Insymbol (scanner) Variables
      =============================
*)

    SY    : SYMBOL;     (* last symbol read by INSYMBOL *)
    ID    : ALFA;       (* identifier from     INSYMBOL *)
    INUM  : INTEGER;    (* integer from        INSYMBOL *)
    RNUM  : REAL;       (* real number from    INSYMBOL *)
    SLENG : INTEGER;    (* string length                *)
    CHARTP: ARRAY[CHAR] OF CHTP;     (* character types *)
    LINE  : ARRAY [1..LLNG] OF CHAR; (* input line      *)
    CC    : INTEGER;    (* character counter            *)
    LL    : INTEGER;    (* length of current line       *)
    LINECOUNT: INTEGER; (* source line counter          *)


(*
   ======
    sets
   ======
*)

    CONSTBEGSYS, TYPEBEGSYS,
    BLOCKBEGSYS, FACBEGSYS, STATBEGSYS : SYMSET;



(*--------------------------------------------------------ERROR-----*)

procedure ERROR( N : INTEGER );
(*
   write error on current line & add to TOT ERR
*)
begin
  if ERRPOS = 0 then write('[**> ', ' ':6);
  if CC > ERRPOS then begin
     write( ' ': CC-ERRPOS, '^', N:2 );
     ERRPOS := CC+3;
     ERRS := ERRS + [N];
  end;
end; { ERROR }

(*-----------------------------------------------------ENDSKIP------

   ENDSKIP changed to just print blanks for skipped symbols.
   This should cause less confusion than the underlining did.
*)

procedure ENDSKIP;    (* underline skipped part of input *)
begin
  while ERRPOS < CC do begin
    write(' ');
    ERRPOS := ERRPOS + 1;
  end;
  SKIPFLAG := FALSE;
end; { ENDSKIP }

procedure FATAL( N : integer ); forward;
procedure NEXTCH; forward;

(*---------------------------------------------------------EMIT-----
   emit actual code into the code table
*)
procedure EMIT(FCT: INTEGER);
begin
   if LC = CMAX then FATAL(6);
   CODE[LC].F := FCT;
   LC := LC+1;
end; { EMIT }

procedure EMIT1(FCT,B: INTEGER);
begin
  if LC = CMAX then FATAL(6);
  with CODE[LC] do begin
    F := FCT;
    Y := B;
  end;
  LC := LC+1;
end; { EMIT1 }

procedure EMIT2(FCT,A,B: INTEGER);
begin
  if LC = CMAX then FATAL(6);
  with CODE[LC] do begin
    F := FCT;
    X := A;
    Y := B;
  end;
  LC := LC+1;
end; { EMIT2 }

(*-----------------------INITTABLES----ERRORMSG----ENTERSTDFCNS-----*)

{$I INIT.MOD }

(*-----------------------------------------------------INSYMBOL-----*)

{$I INSYMBOL.MOD }

(*--------------------------------------------------PRINTTABLES-----
   this procedure prints out the internal compiler and
   interpreter tables.  This procedure is called if the
   DEBUG flag is TRUE.
*)

procedure PRINTTABLES;
var I: INTEGER;
    O: ORDER;
begin
   writeln;
   writeln(' Identifiers          Link  Obj  Typ  Ref  NRM  Lev  Adr');
   for I := BTAB[1].LAST +1 to T do with TAB[I] do
     writeln(I,' ',NAME,LINK:5, ORD(OBJ):5, ORD(TYP):5, REF:5,
             ORD(NORMAL):5, LEV:5, ADR:5);
   writeln(' Blocks    Last LPar PSze Vsze');
   for I := 1 to B do with BTAB[I] do
     writeln(I, LAST:5, LASTPAR:5, PSIZE:5, VSIZE:5);
   writeln;
   writeln(' Arrays    Xtyp Etyp Eref  Low High Elsz Size');
   for I := 1 to A do with ATAB[I] do
     writeln(I, ORD(INXTYP):5, ORD(ELTYP):5,
       ELREF:5, LOW:5, HIGH:5, ELSIZE:5, SIZE:5);
   writeln(' CODE:');
   for I := 0 to LC-1 do begin
     if I MOD 5 = 0 then begin
       writeln; write(I:5)
     end;
     O := CODE[I];
     write(O.F:5);
     if O.F < 31 then
       if O.F < 4 then write(O.X:2, O.Y:5)
                  else write(O.Y:7)
     else write('       ');
     write(',');
   end;
   writeln;
end; { PRINTTABLES }

(*--------------------------------------------------------BLOCK-----*)

{$I BLOCKA.MOD }
{$I BLOCKB.MOD }
{$I BLOCKC.MOD }

(*--------------------------------------------------------FATAL-----*)

procedure FATAL;  (* internal table overflow *)
begin
  if ERRS <> [] then ERRORMSG;
  writeln;
  write( 'COMPILER TABLE for ' );
  case N of
    1 : write( 'IDENTIFIER' );
    2 : write( 'PROCEDURES' );
    3 : write(      'REALS' );
    4 : write(     'ARRAYS' );
    5 : write(     'LEVELS' );
    6 : write(       'CODE' );
    7 : write(    'STRINGS' );
  end;
  writeln( ' is too SMALL' );
  writeln;
  writeln(' Please take this output to the maintainer of ');
  writeln(' this language for your installation '         );
  writeln; writeln;
  writeln(' FATAL termination of Co-Pascal');
  HALT;
end; { FATAL }

(*-------------------------------------------------------NEXTCH-----*)

procedure NEXTCH;   (* read next char; process line end *)
begin
  if CC = LL then begin
    if EOF( SOURCE ) then begin
      writeln;
      writeln(' PROGRAM INCOMPLETE');
      ERRORMSG;
      HALT;
    end;
    if ERRPOS <> 0 then begin
      if SKIPFLAG then endSKIP;
      ERRPOS := 0;
      writeln;
    end;
    LINECOUNT := LINECOUNT + 1;
    write( LINECOUNT:4,'  ' );
    write( LC:5, '  ' );
    LL := 0;
    CC := 0;
    while NOT EOLN(SOURCE) do begin
      LL := LL+1;
      read( SOURCE,CH);
      write(CH);
      LINE[LL] := CH
    end;
    LL := LL + 1;
    writeln;
    readln( SOURCE );
    LINE[LL] := ' ';
  end;
  CC := CC+1;
  CH := LINE[CC];
  if (ORD(CH) < ORD(' ')) then ERROR(60)
end; { NEXTCH }


begin { COMPILE }

(*
   =============================
     check for program heading
   =============================
*)

  INITIALIZE;
  INSYMBOL;
  if SY <> PROGRAMSY then ERROR(3) else begin
    INSYMBOL;
    if SY <> IDENT then ERROR(2) else begin
      PROGNAME := ID;
      INSYMBOL;
      if SY <> LPARENT then ERROR(9) else repeat
        INSYMBOL;
        if SY <> IDENT then ERROR(2) else begin
          if ID = 'INPUT     ' then IFLAG := TRUE
            else if ID = 'OUTPUT    ' then OFLAG := TRUE
              else if ( NOT DFLAG ) then begin
                DFILE := '          ';
                M := 0;
                while ID[m+1] in [ 'A'..'Z', '0'..'9', ':' ]
                  do M := M + 1;
                MOVE( ID, DFILE[11-m], m );
                DFLAG := TRUE;
                writeln( ' DFLAG <- TRUE ', DFILE, m:5 );
              end else ERROR(0);
          INSYMBOL;
        end;
      until SY <> COMMA;
      if SY = RPARENT then INSYMBOL else ERROR(4);
      if NOT OFLAG then ERROR(20)
    end
  end;

  ENTERSTDFCNS;

  with BTAB[1] do begin
   LAST := T;
   LASTPAR := 1;
   PSIZE := 0;
   VSIZE := 0
  end;

(*
   ============
     COMPILE
   ============
*)

  block( BLOCKBEGSYS+STATBEGSYS, FALSE, 1 );

  if (SY <> PERIOD) then ERROR(22);
  EMIT(31);  (* halt *)
  if ( BTAB[2].VSIZE > STMAX-STKINCR * PMAX ) then ERROR(49);
  if DEBUG then PRINTTABLES;
  if ERRS <> [] then begin
    ERRORMSG;
    HALT;
  end;
end; { COMPILE }

(*----------------------------------------------------INTERPRET------*)

overlay procedure INTERPRET;

{$I INTERPT.MOD  }

end; { INTERPRET }

(*---------------------------------------------------P_CODE I/O-----*)

procedure PutBlock( FileName : FNAME );
var ObjFile : file;
    t       : string[ 3];
    len     : integer;

begin
  assign( ObjFile, FileName + '.OBJ' );
  rewrite( ObjFile );
  for len := 1 to 25 do SS[len] := ' ';
  len := length( SFILE );
  MOVE( SFILE[1], SS[11-len], len );
  if DFLAG then MOVE( DFILE[1], SS[11], 10 );
  MOVE( IFLAG, SS[21], 1 );
  MOVE( OFLAG, SS[22], 1 );
  MOVE( DFLAG, SS[23], 1 );
  MOVE( B    , SS[24], 2 );

  blockwrite( ObjFile,    TAB, ( SizeOf(   TAB) DIV 128 )+1 );
  blockwrite( ObjFile,   ATAB, ( SizeOf(  ATAB) DIV 128 )+1 );
  blockwrite( ObjFile,   BTAB, ( SizeOf(  BTAB) DIV 128 )+1 );
  blockwrite( ObjFile,   STAB, ( SizeOf(  STAB) DIV 128 )+1 );
  blockwrite( ObjFile,   CODE, ( SizeOf(  CODE) DIV 128 )+1 );
  blockwrite( ObjFile, RCONST, ( SizeOf(RCONST) DIV 128 )+1 );
  blockwrite( ObjFile,     SS, ( SizeOf(    SS) DIV 128 )+1 );
  close( ObjFile );
end;

procedure GetBlock( FileName : FNAME );

type temptr  = ^tempdat;
     tempdat = array [1..128] of 0..255;

var ObjFile : file;
    a       : temptr;
    temp    : tempdat;
    len     : integer;

  procedure B_read( var varname; q : integer );
  begin
    blockread( ObjFile, varname, ( Q DIV 128 ) );
    blockread( ObjFile, temp, 1 );
    a := ptr( Seg(varname), Ofs(varname) + 128*( Q DIV 128 ) );
    move( temp, a^, ( Q MOD 128 ) );
  end;

begin
  assign( ObjFile, FileName + '.OBJ' );
  reset( ObjFile );
  B_read(    TAB, SizeOf(    TAB ));
  B_read(   ATAB, SizeOf(   ATAB ));
  B_read(   BTAB, SizeOf(   BTAB ));
  B_read(   STAB, SizeOf(   STAB ));
  B_read(   CODE, SizeOf(   CODE ));
  B_read( RCONST, SizeOf( RCONST ));
  B_read(     SS, SizeOf(     SS ));
  len := 1;
  while SFILE[len] = ' ' do len := len+1;
  MOVE( SS[len], SFILE[1],10 );  SFILE[0] := CHR( 11-len );
  MOVE( SS[ 21],    IFLAG, 1 );
  MOVE( SS[ 22],    OFLAG, 1 );
  MOVE( SS[ 23],    DFLAG, 1 );
  MOVE( SS[ 24],        B, 2 );
  if DFLAG then MOVE( SS[11], DFILE[1], 10 );  DFILE[0] := CHR(10);
  if DEBUG then begin
    writeln;
    write('  S: ',SFILE+'.PAS     ');
    if DFLAG then writeln('D: ',DFILE+'.DAT' ) else writeln;
    writeln(' flags I/O/D :',IFLAG:8,OFLAG:6,DFLAG:6,'     B : ',B );
    writeln;
  end;
end;

procedure HELP;
begin
  writeln;
  writeln(' Selection error.  Correct syntax is :  FNAME -X* ');
  writeln;
  writeln(' where FNAME is a legal file name with the .TYP optional ');
  writeln(' and the <X> option is one of the following : ');
  writeln;
  writeln('    C :: compile the source code to P-code ');
  writeln('    E :: execute a previously compiled P-code ');
  writeln('    R :: compile and then execute  ');
  writeln;
  writeln('    * is an optional flag to display debug information ');
  writeln;
  halt;
end;

begin { MAIN }

  if ( ParamCount < 1 ) then HELP;
  SFILE := ParamStr(1);
  for m := 1 to length( SFILE ) do SFILE[m] := UpCase( SFILE[m] );
  assign( SOURCE, SFILE+'.PAS' );
  {$I-}
  reset( SOURCE )
  {$I+};
  if IOresult <> 0 then begin
    writeln('Cannot find file : ', SFILE+'.PAS' );
    halt;
  end;
  writeln; writeln(' ':10,HEADER); writeln;

  if ( ParamCount < 2 ) then begin
    OPTION := 'R';
    DEBUG  := FALSE;
  end else begin
    CmdLine := ParamStr(2);
    if ( CmdLine[1] = '-' ) then OPTION := UpCase( CmdLine[2] ) else HELP;
    if ( CmdLine[3] = '*' ) then DEBUG := TRUE else DEBUG := FALSE;
  end;

  case OPTION of

    'C' : begin
            COMPILE;
            PutBlock( SFILE );
          end;

    'E' : begin
            GetBlock( SFILE );
            INTERPRET;
          end;

    'R' : begin
            COMPILE;
            writeln;
            writeln(' begin execution for : ', PROGNAME );
            writeln;
            INTERPRET;
          end;

    else HELP;
  end;

  writeln;
end.
