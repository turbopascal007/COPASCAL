
(*-------------------------------------------------------INITIALIZE---*)

procedure INITIALIZE;

var I : INTEGER;
    C :    CHAR;

begin

(*
    =================
     character types
    =================
 *)

  SPS['+'] := PLUS;        SPS['-'] := MINUS;
  SPS['*'] := TIMES;       SPS['/'] := RDIV;
  SPS['('] := LPARENT;     SPS[')'] := RPARENT;
  SPS['='] := EQL;         SPS[','] := COMMA;
  SPS['['] := LBRACK;      SPS[']'] := RBRACK;
  SPS['"'] := NEQ;         SPS['&'] := ANDSY;
  SPS[';'] := SEMICOLON;

  for C := CHR( ORDMINCHAR ) to CHR( ORDMAXCHAR ) do case C of

    'A'..'Z' : CHARTP[C] := LETTER;
    'a'..'z' : CHARTP[C] := LOWCASE;
    '0'..'9' : CHARTP[C] := NUMBER;

    '+', '-', '*', '/', '(', ')', '$', '=', ' ', ',',
    '.', '''','[', ']', ':', '^', '_', ';', '{', '}',
    '<', '>' : CHARTP[C] := SPECIAL;

    else CHARTP[C] := ILLEGAL;

  end;

(*
    ===========
       Sets
    ===========
*)

  CONSTBEGSYS := [ PLUS,MINUS,INTCON,REALCON,CHARCON,IDENT    ];
  TYPEBEGSYS  := [ IDENT,ARRAYSY,RECORDSY                     ];
  BLOCKBEGSYS := [ CONSTSY,TYPESY,VARSY,PROCSY,FUNCSY,BEGINSY ];
  FACBEGSYS   := [ INTCON,REALCON,CHARCON,IDENT,LPARENT,NOTSY ];
  STATBEGSYS  := [ BEGINSY,IFSY,WHILESY,REPEATSY,FORSY,CASESY ];
  STANTYPS    := [ NOTYP,INTS,REALS,BOOLS,CHARS               ];

(*
   ===========
     Scalars
   ===========
*)

  LC := 0;
  LL := 0;
  CC := 0;
  CH := ' ';
  ERRPOS :=  0;
  ERRS   := [];
  T := -1;
  A :=  0;
  B :=  1;
  SX := 0;
  C2 := 0;
  DISPLAY[0] := 1;
  IFLAG := FALSE;
  OFLAG := FALSE;
  DFLAG := FALSE;
  SKIPFLAG := FALSE;
  LINECOUNT := -1;

end; { INITIALIZE }

procedure ENTERSTDFCNS;

(*--------------------------------------------------------ENTER-----
   the following procedures enter the apropriate type
   into the associated table for that type.
*)

  procedure ENTER( X0: ALFA; X1: OBJECT; X2: TYPES; X3: INTEGER );
  begin
     T := T+1;       (* enter standard identifier *)
     with TAB[T] do begin
       NAME := X0;
       LINK := T-1;
       OBJ  := X1;
       TYP  := X2;
       REF  := 0;
       NORMAL := TRUE;
       LEV  := 0;
       ADR  := X3;
     end;
  end; { ENTER }

begin
  ENTER('          ',  VARIABLE, NOTYP,  0);
  ENTER('FALSE     ',  KONSTANT, BOOLS,  0);
  ENTER('TRUE      ',  KONSTANT, BOOLS,  1);
  ENTER('REAL      ',     TYPE1, REALS,  1);
  ENTER('CHAR      ',     TYPE1, CHARS,  1);
  ENTER('BOOLEAN   ',     TYPE1, BOOLS,  1);
  ENTER('INTEGER   ',     TYPE1, INTS ,  1);
  ENTER('ABS       ',  FUNKTION, REALS,  0);
  ENTER('SQR       ',  FUNKTION, REALS,  2);
  ENTER('ODD       ',  FUNKTION, BOOLS,  4);
  ENTER('CHR       ',  FUNKTION, CHARS,  5);
  ENTER('ORD       ',  FUNKTION, INTS,   6);
  ENTER('SUCC      ',  FUNKTION, CHARS,  7);
  ENTER('PRED      ',  FUNKTION, CHARS,  8);
  ENTER('ROUND     ',  FUNKTION, INTS,   9);
  ENTER('TRUNC     ',  FUNKTION, INTS,  10);
  ENTER('SIN       ',  FUNKTION, REALS, 11);
  ENTER('COS       ',  FUNKTION, REALS, 12);
  ENTER('EXP       ',  FUNKTION, REALS, 13);
  ENTER('LN        ',  FUNKTION, REALS, 14);
  ENTER('SQRT      ',  FUNKTION, REALS, 15);
  ENTER('ARCTAN    ',  FUNKTION, REALS, 16);
  ENTER('EOF       ',  FUNKTION, BOOLS, 17);
  ENTER('EOLN      ',  FUNKTION, BOOLS, 18);
  ENTER('RANDOM    ',  FUNKTION, INTS,  19);
  ENTER('READ      ', PROZEDURE, NOTYP,  1);
  ENTER('READLN    ', PROZEDURE, NOTYP,  2);
  ENTER('WRITE     ', PROZEDURE, NOTYP,  3);
  ENTER('WRITELN   ', PROZEDURE, NOTYP,  4);
  ENTER('WAIT      ', PROZEDURE, NOTYP,  5);
  ENTER('SIGNAL    ', PROZEDURE, NOTYP,  6);
  ENTER('          ', PROZEDURE, NOTYP,  0);
end; { ENTERSTDFCNS }

procedure ERRORMSG;
const   MSG : array[0..60] of string[40] =
          ( 'UNDEFINED IDENTIFIER',
            'MULTIPLE DEFINITION OF THIS IDENTIFIER',
            'EXPECTED AN IDENTIFIER',
            'PROGRAM MUST begin WITH "PROGRAM"',
            'EXPECTED CLOSING PARENTHESIS ")"',
{  5 }      'EXPECTED A COLON ":"',
            'INCORRECTLY USED SYMBOL',
            'EXPECTED IDENTIFIER OR THE SYMBOL "VAR"',
            'EXPECTED THE SYMBOL "OF"',
            'EXPECTED AN OPENING PARENTHESIS "("',
{ 10 }      'EXPECTED IDENTIFER, "ARRAY" OR "RECORD"',
            'EXPECTED AN OPENING BRACKET "["',
            'EXPECTED A CLOSING BRACKET "]"',
            'EXPECTED ".." WITHOUT INTERVENING BLANKS',
            'EXPECTED A SEMICOLON ";"',
{ 15 }      'BAD RESULT TYPE FOR A FUNCTION',
            'EXPECTED AN EQUAL SIGN "="',
            'EXPECTED BOOLEAN EXPRESSION ',
            'CONTROL VARIABLE OF THE WRONG TYPE',
            'MUST BE MATCHING TYPES',
{ 20 }      '"OUTPUT" IS REQUIRED IN PROGRAM HEADING',
            'THE NUMBER IS TOO LARGE',
            'EXPECT PERIOD ".", CHECK begin-END PAIRS',
            'BAD TYPE FOR A CASE STATEMENT',
            'ILLEGAL CHARACTER',
{ 25 }      'ILLEGAL CONSTANT OR CONSTAT IDENTIFIER',
            'ILLEGAL ARRAY SUBSCRIPT (CHECK TYPE)',
            'ILLEGAL BOUNDS FOR AN ARRAY INDEX',
            'INDEXED VARIABLE MUST BE AN ARRAY',
            'EXPECTED A TYPE IDENFIFIER',
{ 30 }      'UNDEFINED TYPE',
            'VAR WITH FIELD SELECTOR MUST BE RECORD',
            'EXPECTED TYPE "BOOLEAN"',
            'ILLEGAL TYPE FOR ARITHMETIC EXPRESSION',
            'EXPECTED INTEGER FOR "DIV" OR "MOD"',
{ 35 }      'INCOMPATIBLE TYPES FOR COMPARISON',
            'PARAMETER TYPES DO NOT MATCH',
            'EXPECTED A VARIABLE',
            'A STRING MUST HAVE ONE OR MORE CHAR',
            'NUMBER OF PARAMETERS DO NOT MATCH',
{ 40 }      'ILLEGAL PARAMETERS TO "READ"',
            'ILLEGAL PARAMETERS TO "WRITE"',
            'PARAMETER MUST BE OF TYPE "REAL"',
            'PARAMETER MUST BE OF TYPE "INTEGER"',
            'EXPECTED VARIABLE OR CONSTANT',
{ 45 }      'EXPECTED A VARIABLE OR PROCEDURE',
            'TYPES MUST MATCH IN AN ASSIGNMENT',
            'CASE LABEL NOT SAME TYPE AS CASE CLAUSE',
            'ARGUMENT TO STD. FUNCTION OF WRONG TYPE',
            'THE PROGRAM REQUIRES TOO MUCH STORAGE',
{ 50 }      'ILLEGAL SYMBOL FOR A CONSTANT',
            'EXPECTED BECOMES ":="',
            'EXPECTED "THEN"',
            'EXPECTED "UNTIL"',
            'EXPECTED "DO"',
{ 55 }      'EXPECTED "TO" OR "DOWNTO"',
            'EXPECTED "BEGIN"',
            'EXPECTED "END"',
            'EXPECTED ID, CONST, "NOT" OR "("',
            '"INPUT"  IS REQUIRED IN PROGRAM HEADING',
{ 60 }      'CONTROL CHARACTER PRESENT IN SOURCE ');

var K : integer;

begin
  K := 0;
  writeln; writeln(' ERROR MESSAGE(S)');
  while ERRS <> [] do begin
    while NOT ( K in ERRS ) do K := K+1;
    writeln( K:2,'  ',MSG[K] );
    ERRS := ERRS - [K]
  end;
end; { ERRORMSG }
