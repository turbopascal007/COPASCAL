(*$D-,B-,R+,U+ Concurrent Pascal-S *)

Program pascals( input, output );
(* author: N. Wirth, E.T.H. ch--8092 Zurich, 1.3.76 *)
(* modified: M. Ben-Ari, Tel Aviv Univ, 1980 *)
(* C. T. Zahn, Pace Univ, 1988 *)
(* M. Camillone, Pace Univ, 1992 *)

Uses DOS, CRT;

Const DEBUG = true;
(* to control extra output *)
  WAKESEM = false;
(* controls semaphore signal behavior *)
  USEQUANTUM = false;
(* to context switch after quantum or 1 instr. *)
  pmax = 10;
(* max no. of simultaneous processes *)
  stmax = 5000;
(* total stacksize *)
  mainsize = 2000;
(* global data in main process *)
  quantmin = 10;
(* minimum quantum size *)
  quantwidth = 10;
(* variance of quantum size *)
  single = 1;
(* identifies a single communication request *)
  select = 0;
(* integer values *)
  send = 1;
(* of *)
  receive = 2;
(* communication commands *)
  purebool = 3;
(* "direction" for guard only containing Boolean *)
  nkw = 27;
(* no. of keywords *)
  alng = 10;
(* no. of significant chars in ident *)
  llng = 70;
(* input line length *)
  kmax = 5;
(* max no. of significant digits *)
  tmax = 70;
(* size of table *)
  bmax = 20;
(* size of block-table *)
  amax = 10;
(* size of array table *)
  cmax = 500;
(* size of code *)
  lmax = 7;
(* maximum level *)
  smax = 500;
(* size of string table *)
  omax = 70;
(* highest order code *)
  xmax = 30000;
  nmax = 30000;
  lineleng = 80;
(* output line length *)
  linelimit = 400;
(* max lines to print *)

Type symbol = (intcon, charcon, stringsy,
               notsy, plus, minus, times, idiv, imod, andsy, orsy,
               eql, neq, gtr, geq, lss, leq,
               lparent, rparent, lbrack, rbrack, comma, semicolon,
               period, bar, ampersand, arrow, pound,
               colon, becomes, constsy, typesy, varsy, functionsy,
               proceduresy, arraysy, programsy, ident, selectsy,
               beginsy, cobegsy, ifsy, repeatsy, whilesy, forsy,
               endsy, coendsy, elsesy, untilsy, ofsy, dosy, tosy,
               thensy);
  index = -xmax .. +xmax;
  alfa = packed array [1..alng] Of char;
  Object = (konstant, variable, type1, prozedure, funktion);
    types = (notyp, ints, bools, chars, semas, chans, arrays);
    er = (erid, ertyp, erkey, erpun, erpar, ernf,
          61
          erdup, erch, ersh, erln);
    symset = set Of symbol;
    typset = set Of types;
    item = Record
      typ : types;
      ref : index;
    End;
    order = packed Record
      f : -omax .. +omax;
      x : -lmax .. +lmax;
      y : -nmax .. +nmax;
    End;

    Var sy : symbol;
(* last symbol read by insymbol *)
      id : alfa;
(* identifier from insymbol *)
      inum : integer;
(* integer from insymbol *)
      rnum : real;
(* real number from insymbol *)
      sleng : integer;
(* string length *)
      ch : char;
(* last character read from source *)
      line : array[1..llng] Of char;
      cc : integer;
(* character counter *)
      lc : integer;
(* program location counter *)
      ll : integer;
(* length of current line *)
      errs : set Of er;
      errpos : integer;
      progname : alfa;
      skipflag : boolean;
      constbegsys, typebegsys, blockbegsys, facbegsys,
      statbegsys : symset;
      key : array[1..nkw] Of alfa;
      ksy : array[1..nkw] Of symbol;
      sps : array[char] Of symbol;
(* special symbols *)
      t, a, b, sx, c1, c2, k : integer;
(* indices to tables *)
      stantyps : typset;
      display : array[0..lmax] Of integer;
      parseguard : boolean;
      c : char;
(* user's response to questions *)
      Screen, Keys : text;
      tab : array[0..tmax] Of (* identifier table *)
            packed Record
              name : alfa;
              link : index;
              obj : Object;
                typ : types;
                ref : index;
                normal : boolean;
                lev : 0..lmax;
                adr : integer;
              End;
              atab : array[1..amax] Of (* array table *)
                     packed Record
                       inxtyp, eltyp : types;
                       elref, low, high, elsize, size : index;
                     End;
              btab : array[1..bmax] Of (* block table *)
                     packed Record
                       last, lastpar, psize, vsize : index;
                     End;
              stab : packed array[0..smax] Of char;
(* string table *)
              code : array[0..cmax] Of order;
              CODELIST : boolean;
(* for listing of machine code *)
              TRACE : boolean;
(* to trace execution -- wait, signal etc. *)
              ShowInternal : boolean;
(* display sumtab and list of waits & signals *)
              Adaptive : boolean;
(* for Adaptive printout mode of Runtime Graph *)
              Procedure DumpGlobalNames;

              Var k : integer;
              Begin
                62
                writeln;
                writeln;
                writeln('Global Variables:');
                writeln(' ':3, 'FBsema ', ' ', 'OFFSET: ', 5:5 );
                For k := 0 To t Do
                  With tab[k] Do
                    If (lev = 1) And (obj = variable) Then
                      writeln(' ':3, name, ' ', 'OFFSET: ', adr:5 );
                writeln;
                writeln;
              End;
(* DumpGlobalNames *)
              Procedure DateAndTime;

              Var yr, mon, day, wkdy, hr, min, sec, s100 : word;
              Begin
                GetDate( yr, mon, day, wkdy );
                GetTime( hr, min, sec, s100 );
                write( ' ', mon, '/', day, '/', yr, ' -- ' );
                If hr = 0 Then write( '12:' )
                Else If hr > 12 Then write( hr - 12, ':' )
                Else write( hr, ':' );
                If min < 10 Then write( '0' );
                write( min, ':' );
                If sec < 10 Then write( '0' );
                write( sec );
                If hr > 11 Then write( 'pm' )
                Else write( 'am' );
                writeln( ' ----' )
              End;
(* DateAndTime *)
(*$I cpslex.pas *)
(* ------------------------------------------------ BLOCK --- *)
              Procedure block( fsys : symset; isfun : boolean; level : integer );

              Type conrec = 
                            Record
                              tp : types;
                              i : integer
                            End;

              Var dx : integer;
(* data allocation index *)
                prt : integer;
(* t-index of this procedure *)
                prb : integer;
(* b-index of this procedure *)
                x : integer;
              Procedure skip( fsys : symset; n : er );
              Begin
                error(n);
                skipflag := true;
                While Not ( sy In fsys ) Do
                  insymbol;
                If skipflag Then endskip
              End;
(* skip *)
              Procedure test( s1, s2 : symset; n : er );
              Begin
                If Not ( sy In s1 ) Then skip( s1+s2, n )
              End;
(* test *)
              Procedure testsemicolon;
              Begin
                If sy = semicolon Then insymbol
                Else error( erpun );
                test( [ident]+blockbegsys, fsys, erkey )
              End;
(* testsemicolon *)
              Procedure enter( id : alfa; k : Object );

              Var j, l : integer;
              Begin
                If t = tmax Then fatal(1)
                  63
                Else
                  Begin
                    tab[0].name := id;
                    j := btab[display[level]].last;
                    l := j;
                    While tab[j].name <> id Do
                      j := tab[j].link;
                    If j <> 0 Then error( erdup )
                    Else
                      Begin
                        t := t+1;
                        With tab[t] Do
                          Begin
                            name := id;
                            link := l;
                            obj := k;
                            typ := notyp;
                            ref := 0;
                            lev := level;
                            adr := 0
                          End;
                        btab[display[level]].last := t
                      End
                  End
              End;
(* enter *)
              Function loc( id : alfa ) : integer;

              Var i, j : integer;
              Begin
(* locate id in table *)
                i := level;
                tab[0].name := id;
(* sentinel *)
                Repeat
                  j := btab[display[i]].last;
                  While tab[j].name <> id Do
                    j := tab[j].link;
                  i := i-1
                Until (i<0) Or (j<>0);
                If j = 0 Then error( ernf );
                loc := j
              End;
(* loc *)
              Procedure entervariable;
              Begin
                If sy = ident Then
                  Begin
                    enter( id, variable );
                    insymbol
                  End
                Else error( erid )
              End;
(* entervariable *)
              Procedure constant( fsys : symset; Var c : conrec );

              Var x, sign : integer;
              Begin
                c.tp := notyp;
                c.i := 0;
                test( constbegsys, fsys, erkey );
                If sy In constbegsys Then
                  Begin
                    If sy = charcon Then
                      Begin
                        c.tp := chars;
                        c.i := inum;
                        insymbol
                      End
                    Else
                      Begin
                        sign := 1;
                        If sy In [plus,minus] Then
                          Begin
                            If sy = minus Then sign := -1;
                            insymbol
                          End;
                        If sy = ident Then
                          Begin
                            x := loc(id);
                            If x <> 0 Then
                              64
                              If tab[x].obj <> konstant Then error( ertyp )
                            Else
                              Begin
                                c.tp := tab[x].typ;
                                c.i := sign*tab[x].adr
                              End;
                            insymbol
                          End
                        Else If sy = intcon Then
                               Begin
                                 c.tp := ints;
                                 c.i := sign*inum;
                                 insymbol
                               End
                        Else skip( fsys, erkey )
                      End
                  End
              End;
(* constant *)
              Procedure typ( fsys : symset; Var tp : types; Var rf, sz : integer );

              Var x : integer;
                eltp : types;
                elrf : integer;
                elsz, offset, t0, t1 : integer;
              Procedure arraytyp( Var aref, arsz : integer );

              Var eltp : types;
                low, high : conrec;
                elrf, elsz : integer;
              Begin
                constant( [colon,rbrack,ofsy]+fsys, low );
                If sy = colon Then insymbol
                Else error( erpun );
                constant( [rbrack,comma,ofsy]+fsys, high );
                If high.tp <> low.tp Then
                  Begin
                    error( ertyp );
                    high.i := low.i
                  End;
                enterarray( low.tp, low.i, high.i );
                aref := a;
                If sy = comma Then
                  Begin
                    insymbol;
                    eltp := arrays;
                    arraytyp( elrf, elsz )
                  End
                Else
                  Begin
                    If sy = rbrack Then insymbol
                    Else error(erpun);
                    If sy = ofsy Then insymbol
                    Else error(erkey);
                    typ( fsys, eltp, elrf, elsz )
                  End;
                With atab[aref] Do
                  Begin
                    arsz := (high-low+1)*elsz;
                    size := arsz;
                    eltyp := eltp;
                    elref := elrf;
                    elsize := elsz
                  End
              End;
(* arraytyp *)
              Begin
(* typ *)
                tp := notyp;
                rf := 0;
                sz := 0;
                test( typebegsys, fsys, erid );
                If sy In typebegsys Then
                  Begin
                    If sy = ident Then
                      Begin
                        x := loc(id);
                        If x <> 0 Then
                          With tab[x] Do
                            If obj <> type1 Then
                              error( ertyp )
                              65
                            Else
                              Begin
                                tp := typ;
                                rf := ref;
                                sz := adr;
                                If tp = notyp Then error( ertyp )
                              End;
                        insymbol
                      End
                    Else If sy = arraysy Then
                           Begin
                             insymbol;
                             If sy = lbrack Then insymbol
                             Else error(erpun);
                             tp := arrays;
                             arraytyp( rf, sz )
                           End
                    Else test( fsys, [], erkey )
                  End
              End;
(* typ *)
              Procedure parameterlist;
(* formal parameter list *)

              Var 
                tp : types;
                rf, sz, x, t0 : integer;
                valpar : boolean;
              Begin
                insymbol;
                tp := notyp;
                rf := 0;
                sz := 0;
                test( [ident,varsy], fsys+[rparent], erpar );
                While sy In [ident,varsy] Do
                  Begin
                    If sy <> varsy Then
                      valpar := true
                    Else
                      Begin
                        insymbol;
                        valpar := false
                      End;
                    t0 := t;
                    entervariable;
                    While sy = comma Do
                      Begin
                        insymbol;
                        entervariable
                      End;
                    If sy = colon Then
                      Begin
                        insymbol;
                        If sy <> ident Then error( erid )
                        Else
                          Begin
                            x := loc(id);
                            insymbol;
                            If x <> 0 Then
                              With tab[x] Do
                                If obj <> type1 Then error(ertyp)
                                Else
                                  Begin
                                    tp := typ;
                                    rf := ref;
                                    If valpar Then sz := adr
                                    Else sz := 1
                                  End;
                          End;
                        test([semicolon,rparent],
                             [comma,ident]+fsys, erpun)
                      End
                    Else error(erpun);
                    While t0 < t Do
                      66
                      Begin
                        t0 := t0+1;
                        With tab[t0] Do
                          Begin
                            typ := tp;
                            ref := rf;
                            normal := valpar;
                            adr := dx;
                            lev := level;
                            dx := dx+sz
                          End
                      End;
                    If sy <> rparent Then
                      Begin
                        If sy = semicolon Then insymbol
                        Else error(erpun);
                        test( [ident,varsy], [rparent]+fsys, erkey )
                      End
                  End;
(* while *)
                If sy = rparent Then
                  Begin
                    insymbol;
                    test( [semicolon,colon], fsys, erkey )
                  End
                Else error(erpun)
              End;
(* parameterlist *)
              Procedure constantdeclaration;

              Var c : conrec;
              Begin
                insymbol;
                test( [ident], blockbegsys, erid );
                While sy = ident Do
                  Begin
                    enter( id, konstant );
                    insymbol;
                    If sy = eql Then insymbol
                    Else error(erpun);
                    constant( [semicolon,comma,ident]+fsys, c );
                    tab[t].typ := c.tp;
                    tab[t].ref := 0;
                    tab[t].adr := c.i;
                    testsemicolon
                  End
              End;
(* constantdeclaration *)
              Procedure typedeclaration;

              Var tp : types;
                rf, sz, t1 : integer;
              Begin
                insymbol;
                test( [ident], blockbegsys, erid );
                While sy = ident Do
                  Begin
                    enter( id, type1 );
                    t1 := t;
                    insymbol;
                    If sy = eql Then insymbol
                    Else error(erpun);
                    typ( [semicolon,comma,ident]+fsys, tp, rf, sz );
                    With tab[t1] Do
                      Begin
                        typ := tp;
                        ref := rf;
                        adr := sz
                      End;
                    testsemicolon
                  End
              End;
(* typedeclaration *)
              Procedure variabledeclaration;

              Var t0, t1, rf, sz : integer;
                tp : types;
                67
              Begin
                insymbol;
                While sy = ident Do
                  Begin
                    t0 := t;
                    entervariable;
                    While sy = comma Do
                      Begin
                        insymbol;
                        entervariable
                      End;
                    If sy = colon Then insymbol
                    Else error( erpun );
                    t1 := t;
                    typ( [semicolon,comma,ident]+fsys, tp, rf, sz );
                    While t0 < t1 Do
                      Begin
                        t0 := t0+1;
                        With tab[t0] Do
                          Begin
                            typ := tp;
                            ref := rf;
                            lev := level;
                            adr := dx;
                            normal := true;
                            dx := dx+sz
                          End
                      End;
                    testsemicolon
                  End
              End;
(* variabledeclaration *)
              Procedure procdeclaration;

              Var isfun : boolean;
              Begin
                isfun := (sy = functionsy);
                insymbol;
                If sy <> ident Then
                  Begin
                    error(erid);
                    id := ' '
                  End;
                If isfun Then enter(id, funktion)
                Else enter(id, prozedure);
                tab[t].normal := true;
                insymbol;
                block( [semicolon]+fsys, isfun, level+1 );
                If sy = semicolon Then insymbol
                Else error(erpun);
                emit( 32+ord(isfun)) (* exit *)
              End;
(* procdeclaration *)
(* ---------------------------------------------- statement *)
              Procedure statement( fsys : symset );

              Var i : integer;
                x : item;
              Procedure expression( fsys : symset; Var x : item );
              forward;
              Procedure selector( fsys : symset; Var v : item );

              Var x : item;
                a, j : integer;
              Begin
                If sy <> lbrack Then error(ertyp);
                Repeat
                  insymbol;
                  expression( fsys+[comma,rbrack], x );
                  If v.typ <> arrays Then error(ertyp)
                    68
                  Else
                    Begin
                      a := v.ref;
                      If atab[a].inxtyp <> x.typ Then error(ertyp)
                      Else emit1(21,a);
                      v.typ := atab[a].eltyp;
                      v.ref := atab[a].elref
                    End
                Until sy <> comma;
                If sy = rbrack Then insymbol
                Else error(erpun);
                test( fsys, [], erkey )
              End;
(* selector *)
              Procedure call( fsys : symset; i : integer );

              Var x : item;
                lastp, cp, k : integer;
              Begin
                emit1(18,i);
(* mark stack *)
                lastp := btab[tab[i].ref].lastpar;
                cp := i;
                If sy = lparent Then
                  Begin
(* actual parameter list *)
                    Repeat
                      insymbol;
                      If cp >= lastp Then error(erpar)
                      Else
                        Begin
                          cp := cp+1;
                          If tab[cp].normal Then
                            Begin
(* value parameter *)
                              expression(fsys+[comma,colon,rparent], x);
                              If x.typ = tab[cp].typ Then
                                Begin
                                  If x.ref <> tab[cp].ref Then
                                    error(ertyp)
                                  Else If x.typ = arrays Then
                                         emit1(22, atab[x.ref].size)
                                End
                              Else If x.typ <> notyp Then error(ertyp)
                            End
                          Else
                            Begin
(* variable parameter *)
                              If sy <> ident Then error(erid)
                              Else
                                Begin
                                  k := loc(id);
                                  insymbol;
                                  If k <> 0 Then
                                    Begin
                                      If tab[k].obj <> variable Then
                                        error(erpar);
                                      x.typ := tab[k].typ;
                                      x.ref := tab[k].ref;
                                      If tab[k].normal Then
                                        emit2(0,tab[k].lev,tab[k].adr)
                                      Else
                                        emit2(1,tab[k].lev,tab[k].adr);
                                      If sy = lbrack Then
                                        selector(fsys+[comma,colon,
                                                 rparent],x);
                                      If (x.typ<>tab[cp].typ)
                                         Or (x.ref<>tab[cp].ref) Then
                                        error(ertyp)
                                    End
                                    69
                                End
                            End
                        End;
                      test([comma,rparent], fsys, erkey)
                    Until sy <> comma;
                    If sy = rparent Then insymbol
                    Else error(erpun)
                  End;
                If cp < lastp Then error(erpar);
(* too few parms *)
                emit1(19, btab[tab[i].ref].psize-1);
                If tab[i].lev < level Then
                  emit2(3,tab[i].lev, level)
              End;
(* call *)
              Function resulttype( a,b : types ) : types;
              Begin
                If (a>ints) Or (b>ints) Then
                  Begin
                    error(ertyp);
                    resulttype := notyp
                  End
                Else If (a=notyp) Or (b=notyp) Then
                       resulttype := notyp
                Else
                  resulttype := ints
              End;
(* resulttype *)
              Procedure expression;

              Var y : item;
                op : symbol;
              Procedure simpleexpression(fsys : symset; Var x : item);

              Var y : item;
                op : symbol;
              Procedure term(fsys : symset; Var x : item);

              Var y : item;
                op : symbol;
                ts : typset;
              Procedure factor(fsys : symset; Var x : item);

              Var i,f : integer;
              Begin
                x.typ := notyp;
                x.ref := 0;
                test(facbegsys, fsys, erpun);
                While sy In facbegsys Do
                  Begin
                    If sy = ident Then
                      Begin
                        i := loc(id);
                        insymbol;
                        With tab[i] Do
                          Case obj Of 
                            konstant:
                                      Begin
                                        x.typ := typ;
                                        x.ref := 0;
                                        emit1(24,adr)
                                      End;
                            variable:
                                      Begin
                                        x.typ := typ;
                                        x.ref := ref;
                                        If sy = lbrack Then
                                          Begin
                                            If normal Then
                                              f := 0
                                            Else f := 1;
                                            emit2(f,lev,adr);
                                            70
                                            selector(fsys,x);
                                            If x.typ In stantyps Then
                                              emit(34)
                                          End
                                        Else
                                          Begin
                                            If x.typ In stantyps Then
                                              If normal Then
                                                f := 1
                                            Else f := 2
                                            Else
                                              If normal Then
                                                f := 0
                                            Else f := 1;
                                            emit2(f,lev,adr)
                                          End
                                      End;
                            type1, prozedure :
                                               error(ertyp);
                            funktion :
                                       Begin
                                         x.typ := typ;
                                         If lev <> 0 Then
                                           call(fsys,i)
                                         Else emit1(8,adr)
                                       End
                          End
(* with case *)
                      End
                    Else If sy In [charcon,intcon] Then
                           Begin
                             If sy = charcon Then
                               x.typ := chars
                             Else x.typ := ints;
                             emit1(24,inum);
                             x.ref := 0;
                             insymbol
                           End
                    Else If sy = lparent Then
                           Begin
                             insymbol;
                             expression(fsys+[rparent],x);
                             If sy = rparent Then insymbol
                             Else error(erpun)
                           End
                    Else If sy = notsy Then
                           Begin
                             insymbol;
                             factor(fsys,x);
                             If x.typ = bools Then emit(35)
                             Else If x.typ <> notyp Then
                                    error(ertyp)
                           End;
                    test(fsys,facbegsys,erkey)
                  End
              End;
(* factor *)
              Begin
(* term *)
                factor(fsys+[times,idiv,imod,andsy],x);
                While sy In [times,idiv,imod,andsy] Do
                  Begin
                    71
                    op := sy;
                    insymbol;
                    factor(fsys+[times,idiv,imod,andsy],y);
                    If op = times Then
                      Begin
                        x.typ := resulttype(x.typ,y.typ);
                        If x.typ = ints Then emit(57)
                      End
                    Else If op = andsy Then
                           Begin
                             If (x.typ = bools) And (y.typ = bools) Then
                               emit(56)
                             Else
                               Begin
                                 If (x.typ <> notyp)
                                    And (y.typ <> notyp) Then
                                   error(ertyp);
                                 x.typ := notyp
                               End
                           End
                    Else (* op in [idiv,imod] *)
                      Begin
                        If (x.typ = ints) And (y.typ = ints) Then
                          If op = idiv Then emit(58)
                        Else emit(59)
                        Else
                          Begin
                            If (x.typ <> notyp)
                               And (y.typ <> notyp) Then
                              error(ertyp);
                            x.typ := notyp
                          End
                      End
                  End
              End;
(* term *)
              Begin
(* simpleexpression *)
                If sy In [plus,minus] Then
                  Begin
                    op := sy;
                    insymbol;
                    term(fsys+[plus,minus],x);
                    If x.typ > ints Then error(ertyp)
                    Else If op = minus Then emit(36)
                  End
                Else
                  term(fsys+[plus,minus,orsy],x);
                While sy In [plus,minus,orsy] Do
                  Begin
                    op := sy;
                    insymbol;
                    term(fsys+[plus,minus,orsy],y);
                    If op = orsy Then
                      Begin
                        If (x.typ = bools) And (y.typ = bools) Then
                          emit(51)
                        Else
                          Begin
                            If (x.typ <> notyp)
                               And (y.typ <> notyp) Then
                              error(ertyp);
                            x.typ := notyp
                          End
                      End
                      72
                    Else
                      Begin
                        x.typ := resulttype(x.typ,y.typ);
                        If x.typ = ints Then
                          If op = plus Then emit(52)
                        Else emit(53)
                      End
                  End
              End;
(* simpleexpression *)
              Begin
(* expression *)
                simpleexpression(fsys+[eql,neq,lss,leq,gtr,geq],x);
                If sy In [eql,neq,lss,leq,gtr,geq] Then
                  Begin
                    op := sy;
                    insymbol;
                    simpleexpression(fsys,y);
                    If (x.typ In [notyp,ints,bools,chars])
                       And (x.typ = y.typ) Then
                      Case op Of 
                        eql : emit(45);
                        neq : emit(46);
                        lss : emit(47);
                        leq : emit(48);
                        gtr : emit(49);
                        geq : emit(50)
                      End
                    Else error(ertyp);
                    x.typ := bools
                  End
              End;
(* expression *)
              Procedure assignment(lv,ad : integer);

              Var x,y : item;
                f : integer;
(* tab[i].obj in [variable,prozedure] *)
              Begin
                x.typ := tab[i].typ;
                x.ref := tab[i].ref;
                If tab[i].normal Then f := 0
                Else f := 1;
                emit2(f,lv,ad);
                If sy = lbrack Then
                  selector([becomes,eql]+fsys,x);
                If sy = becomes Then
                  insymbol
                Else error(erpun);
                If x.typ = semas Then
                  emit(37);
(* for double store *)
                expression(fsys,y);
                If x.typ = semas Then
                  Begin
(* semaphore initialization *)
                    If y.typ = ints Then
                      Begin
                        emit(38);
(* field 2 of sema set to nilproc *)
                        emit1(24,1);
                        emit(52);
                        emit1(24,-1);
                        emit(38);
                      End
                    Else error(ertyp)
                  End
                Else If x.typ = y.typ Then
                       Begin
                         If x.typ In stantyps Then emit(38)
                         Else If x.ref <> y.ref Then error(ertyp)
                                73
                         Else If x.typ = arrays Then
                                emit1(23,atab[x.ref].size)
                       End
                Else error(ertyp)
              End;
(* assignment *)
              Procedure compoundstatement;
              Begin
                insymbol;
                statement([semicolon,endsy]+fsys);
                While sy In [semicolon]+statbegsys Do
                  Begin
                    If sy = semicolon Then insymbol
                    Else error(erpun);
                    statement([semicolon,endsy]+fsys)
                  End;
                If sy = endsy Then insymbol
                Else error(erkey)
              End;
(* compoundstatement *)
              Procedure parblock;

              Var lc1 : integer;
              Procedure process;
              Begin
                insymbol;
(* wait on FBsema *)
                emit2(0,1,5);
                emit(6);
                emit1(4,level);
(* fork new child *)
                lc1 := lc;
                emit1(10,0);
(* branch around *)
                statement([semicolon,bar,coendsy]+fsys);
                While sy In [semicolon]+statbegsys Do
                  Begin
                    If sy = semicolon Then insymbol
                    Else error(erpun);
                    statement([semicolon,bar,coendsy]+fsys)
                  End;
                emit(5);
(* kill child *)
                code[lc1].y := lc (* fix early branch *)
              End;
(* process *)
              Begin
                process;
                While sy = bar Do
                  process;
                If sy = coendsy Then insymbol
                Else error(erkey);
                emit(9) (* put parent to sleep *)
              End;
(* compoundstatement *)
              Procedure ifstatement;

              Var x : item;
                lc1, lc2 : integer;
              Begin
                insymbol;
                expression(fsys+[thensy,dosy],x);
                If Not (x.typ In [bools,notyp]) Then error(ertyp);
                lc1 := lc;
                emit(11);
(* jmpc *)
                If sy = thensy Then insymbol
                Else error(erkey);
                statement(fsys+[elsesy]);
                If sy = elsesy Then
                  Begin
                    insymbol;
                    lc2 := lc;
                    emit(10);
                    code[lc1].y := lc;
                    statement(fsys);
                    74
                    code[lc2].y := lc
                  End
                Else
                  code[lc1].y := lc
              End;
(* ifstatement *)
              Procedure repeatstatement;

              Var x : item;
                lc1 : integer;
              Begin
                lc1 := lc;
                insymbol;
                statement([semicolon,untilsy]+fsys);
                While sy In [semicolon]+statbegsys Do
                  Begin
                    If sy = semicolon Then insymbol
                    Else error(erpun);
                    statement([semicolon,untilsy]+fsys)
                  End;
                If sy = untilsy Then
                  Begin
                    insymbol;
                    expression(fsys,x);
                    If Not (x.typ In [bools,notyp]) Then error(ertyp);
                    emit1(11,lc1)
                  End
                Else error(erkey)
              End;
(* repeatstatement *)
              Procedure whilestatement;

              Var x : item;
                lc1,lc2 : integer;
              Begin
                insymbol;
                lc1 := lc;
                expression(fsys+[dosy],x);
                If Not (x.typ In [bools,notyp]) Then error(ertyp);
                lc2 := lc;
                emit(11);
                If sy = dosy Then insymbol
                Else error(erkey);
                statement(fsys);
                emit1(10,lc1);
                code[lc2].y := lc
              End;
(* whilestatement *)
              Procedure forstatement;

              Var cvt : types;
                x : item;
                i,lc1,lc2 : integer;
              Begin
                insymbol;
                If sy = ident Then
                  Begin
                    i := loc(id);
                    insymbol;
                    If i = 0 Then cvt := ints
                    Else If tab[i].obj = variable Then
                           Begin
                             cvt := tab[i].typ;
                             If Not tab[i].normal Then error(ertyp)
                             Else emit2(0,tab[i].lev,tab[i].adr);
                             If Not (cvt In [notyp,ints,bools,chars]) Then
                               error(ertyp)
                           End
                    Else
                      Begin
                        error(ertyp);
                        cvt := ints
                      End
                  End
                  75
                Else
                  skip([becomes,tosy,dosy]+fsys,erid);
                If sy = becomes Then
                  Begin
                    insymbol;
                    expression([tosy,dosy]+fsys,x);
                    If x.typ <>cvt Then error(ertyp)
                  End
                Else
                  skip([tosy,dosy]+fsys,erpun);
                If sy = tosy Then
                  Begin
                    insymbol;
                    expression([dosy]+fsys,x);
                    If x.typ <> cvt Then error(ertyp)
                  End
                Else
                  skip([dosy]+fsys,erkey);
                lc1 := lc;
                emit(14);
                If sy = dosy Then insymbol
                Else error(erkey);
                lc2 := lc;
                statement(fsys);
                emit1(15,lc2);
                code[lc1].y := lc
              End;
(* forstatement *)
              Procedure standproc(n : integer);

              Var i,f : integer;
                x,y : item;
              Begin
                Case n Of 
                  1,2 : (* read *)
                        Begin
                          If sy = lparent Then
                            Begin
                              Repeat
                                insymbol;
                                If sy <> ident Then error(erid)
                                Else
                                  Begin
                                    i := loc(id);
                                    insymbol;
                                    If i <> 0 Then
                                      If tab[i].obj <> variable Then
                                        error(ertyp)
                                    Else
                                      Begin
                                        x.typ := tab[i].typ;
                                        x.ref := tab[i].ref;
                                        If tab[i].normal Then
                                          f := 0
                                        Else f := 1;
                                        emit2(f,tab[i].lev,tab[i].adr);
                                        If sy = lbrack Then
                                          selector(fsys+[comma,rparent],x);
                                        If x.typ In [ints,chars,notyp] Then
                                          emit1(27,ord(x.typ))
                                        Else error(ertyp)
                                      End
                                  End;
                                test([comma,rparent],fsys,erkey)
                              Until sy <> comma;
                              If sy = rparent Then insymbol
                              Else error(erpun)
                            End;
                          76
                          If n = 2 Then emit(62)
                        End;
                  3,4 :
                        Begin
(* write *)
                          If TRACE Then emit(12);
                          If sy = lparent Then
                            Begin
                              Repeat
                                insymbol;
                                If sy = stringsy Then
                                  Begin
                                    emit1(24,sleng);
                                    emit1(28,inum);
                                    insymbol
                                  End
                                Else
                                  Begin
                                    expression(fsys+[comma,colon,rparent],x);
                                    If Not (x.typ In stantyps) Then
                                      error(ertyp);
                                    emit1(29,ord(x.typ))
                                  End
                              Until sy <> comma;
                              If sy = rparent Then insymbol
                              Else error(erpun)
                            End;
                          If n = 4 Then emit(63);
                          If TRACE Then emit(13)
                        End;
                  5,6 : (* wait, signal *)
                        If sy <> lparent Then error(erpun)
                        Else
                          Begin
                            insymbol;
                            If sy <> ident Then error(erid)
                            Else
                              Begin
                                i := loc(id);
                                insymbol;
                                If i <> 0 Then
                                  If tab[i].obj <> variable Then
                                    error(ertyp)
                                Else
                                  Begin
                                    x.typ := tab[i].typ;
                                    x.ref := tab[i].ref;
                                    If tab[i].normal Then
                                      f := 0
                                    Else f := 1;
                                    emit2(f,tab[i].lev,tab[i].adr);
                                    If sy = lbrack Then
                                      selector(fsys+[rparent],x);
                                    If x.typ = semas Then
                                      emit(n+1)
                                    Else error(ertyp)
                                  End
                              End;
                            If sy = rparent Then insymbol
                            Else error(erpun)
                          End;
                  77
                  7 : (* halt *)
                      emit(31);
                  8 : (* abort *)
                      emit(17);
                  9 :
                      Begin
(* getchannel *)
                        If sy <> lparent Then error(erpun)
                        Else
                          Begin
                            insymbol;
                            If sy <> ident Then error(erid)
                            Else
                              Begin
                                i := loc(id);
                                insymbol;
                                If i <> 0 Then
                                  If tab[i].obj <> variable Then
                                    error(ertyp)
                                Else
                                  Begin
                                    x.typ := tab[i].typ;
                                    x.ref := tab[i].ref;
                                    emit1(24,i);
(* load channel *)
                                    If sy = lbrack Then
                                      selector(fsys+[rparent],x);
                                    If x.typ = chans Then
                                      emit(42)
                                    Else error(ertyp)
                                  End
                              End;
                            If sy = rparent Then insymbol
                            Else error(erpun)
                          End
                      End;
(* getchannel *)
                  10 :
                       Begin
(* send *)
                         If sy <> lparent Then error(erpun)
                         Else
                           Begin
                             If Not parseguard Then emit(24);
(* sentinel *)
                             insymbol;
                             If sy = ident Then
                               Begin
                                 i := loc(id);
                                 insymbol;
                                 If i <> 0 Then
                                   If tab[i].obj <> variable Then
                                     error(ertyp)
                                 Else
                                   Begin
                                     x.typ := tab[i].typ;
                                     x.ref := tab[i].ref;
                                     emit2(1,tab[i].lev,tab[i].adr);
                                     If sy = lbrack Then
                                       selector(fsys+[rparent,comma],x)
                                   End
                               End
                             Else
                               Begin
                                 expression(fsys+[comma,rparent],x);
                                 If Not (x.typ In stantyps) Then
                                   error(ertyp)
                                   78
                               End;
                             If sy <> comma Then error(erpun)
                             Else insymbol;
                             If sy <> ident Then error(erid)
                             Else
                               Begin
                                 i := loc(id);
                                 insymbol;
                                 If i <> 0 Then
                                   If tab[i].obj <> variable Then
                                     error(ertyp)
                                 Else
                                   Begin
                                     x.typ := tab[i].typ;
                                     x.ref := tab[i].ref;
                                     emit1(24,i);
(* load channel *)
                                     If sy = lbrack Then
                                       selector(fsys+[rparent],x);
                                     If x.typ <> chans Then error(ertyp)
                                   End
                               End;
                             emit1(41,send);
(* post *)
                             If Not parseguard Then emit1(40,single);
(* comm *)
                             If sy = rparent Then insymbol
                             Else error(erpun)
                           End
                       End;
(* send *)
                  11 :
                       Begin
(* receive *)
                         If sy <> lparent Then error(erpun)
                         Else
                           Begin
                             If Not parseguard Then emit(24);
(* sentinel *)
                             insymbol;
                             If sy <> ident Then error(erid)
                             Else
                               Begin
                                 i := loc(id);
                                 insymbol;
                                 If i <> 0 Then
                                   If tab[i].obj <> variable Then
                                     error(ertyp)
                                 Else
                                   Begin
                                     x.typ := tab[i].typ;
                                     x.ref := tab[i].ref;
                                     emit1(24,i);
(* load channel *)
                                     If sy = lbrack Then
                                       selector(fsys+[comma,rparent],x);
                                     If x.typ <> chans Then error(ertyp)
                                   End
                               End;
                             If sy <> comma Then error(erpun)
                             Else insymbol;
                             If sy <> ident Then error(erid)
                             Else
                               Begin
                                 i := loc(id);
                                 insymbol;
                                 If i <> 0 Then
                                   If tab[i].obj <> variable Then
                                     error(ertyp)
                                 Else
                                   Begin
                                     79
                                     x.typ := tab[i].typ;
                                     x.ref := tab[i].ref;
                                     If tab[i].normal Then
                                       f := 0
                                     Else f := 1;
                                     emit2(f,tab[i].lev,tab[i].adr);
                                     If sy = lbrack Then
                                       selector(fsys+[rparent],x)
                                   End
                               End;
                             emit1(41,receive);
(* post *)
                             If Not parseguard Then emit1(40,single);
(* comm *)
                             If sy = rparent Then insymbol
                             Else error(erpun)
                           End
                       End;
(* receive *)
                End
(* case *)
              End;
(* standproc *)
              Procedure selectstatement;

              Type jmpary = array[0..50] Of integer;

              Var lc1, i : integer;
                lc3 : jmpary;
              Procedure guardcomm( Var lc1 : integer; Var lc3 : jmpary );

              Var lc2 : integer;
              Procedure guard( Var lc1, lc2 : integer );

              Var x : item;
              Begin
                parseguard := true;
                If (id = 'send ') Or (id = 'receive ') Then
                  Begin
                    statement( fsys+[arrow] );
                    lc2 := lc;
                    emit(10);
                    lc1 := -1 (* no boolean *)
                  End
                Else
                  Begin
                    expression( fsys+[ampersand,arrow], x );
                    If Not (x.typ In [bools,notyp]) Then error(ertyp);
                    lc1 := lc;
                    emit(11);
(* jmpc *)
                    If sy = ampersand Then
                      Begin
                        insymbol;
                        If (id = 'send ') Or (id = 'receive ') Then
                          statement( fsys+[arrow] )
                        Else error(erkey)
                      End
                    Else
                      emit(43);
(* post pure Boolean *)
                    lc2 := lc;
                    emit(10)
                  End;
                parseguard := false
              End;
(* guard *)
              Begin
(* guardcomm *)
                80
                guard( lc1, lc2 );
                If sy = arrow Then insymbol
                Else error(erpun);
                statement( fsys+[pound] );
(* commands *)
                lc3[0] := lc3[0] + 1;
                lc3[lc3[0]] := lc;
                emit(10);
(* jmp to end *)
                code[lc2].y := lc
              End;
(* guardcomm *)
              Begin
(* selectstatement *)
                emit1(24,select);
(* enter select statement block - push sentinel *)
                lc3[0] := 0;
                insymbol;
                guardcomm( lc1, lc3 );
                If lc1 <> -1 Then
                  code[lc1].y := lc;
                While sy = pound Do
                  Begin
                    insymbol;
                    guardcomm( lc1, lc3 );
                    If lc1 <> -1 Then
                      code[lc1].y := lc
                  End;
                If sy = endsy Then insymbol
                Else error(erkey);
                emit1(40,select);
(* comm *)
                For i := 1 To lc3[0] Do
                  code[lc3[i]].y := lc
              End;
(* selectstatement *)
              Begin
(* statement *)
                If sy In statbegsys+[ident] Then
                  Case sy Of 
                    ident :
                            Begin
                              i := loc(id);
                              insymbol;
                              If i <> 0 Then
                                Case tab[i].obj Of 
                                  konstant,type1 : error(ertyp);
                                  variable : assignment(tab[i].lev,tab[i].adr);
                                  prozedure :
                                              If tab[i].lev <> 0 Then call(fsys,i)
                                              Else standproc(tab[i].adr);
                                  funktion :
                                             If tab[i].ref = display[level] Then
                                               assignment(tab[i].lev+1,0)
                                             Else error(ertyp)
                                End
(* case *)
                            End;
                    beginsy : compoundstatement;
                    cobegsy : parblock;
                    ifsy : ifstatement;
                    whilesy : whilestatement;
                    repeatsy : repeatstatement;
                    81
                    forsy : forstatement;
                    selectsy : selectstatement
                  End;
(* case *)
                test(fsys,[],erpun)
              End;
(* statement *)
              Begin
(* block *)
                dx := 5;
(* global FBsema variable *)
                If level = 1 Then dx := dx+2;
                prt := t;
                If level > lmax Then fatal(5);
                test([lparent,colon,semicolon],fsys,erpun);
                enterblock;
                display[level] := b;
                prb := b;
                tab[prt].typ := notyp;
                tab[prt].ref := prb;
                If (sy = lparent) And (level > 1) Then
                  parameterlist;
                btab[prb].lastpar := t;
                btab[prb].psize := dx;
                If isfun Then
                  If sy = colon Then
                    Begin
                      insymbol;
(* function type *)
                      If sy = ident Then
                        Begin
                          x := loc(id);
                          insymbol;
                          If x <> 0 Then
                            If tab[x].obj <> type1 Then
                              error(ertyp)
                          Else If tab[x].typ In stantyps Then
                                 tab[prt].typ := tab[x].typ
                          Else error(ertyp)
                        End
                      Else skip([semicolon]+fsys,erid)
                    End
                Else error(erpun);
                If sy = semicolon Then insymbol
                Else error(erpun);
                Repeat
                  If sy = constsy Then constantdeclaration;
                  If sy = typesy Then typedeclaration;
                  If sy = varsy Then variabledeclaration;
                  btab[prb].vsize := dx;
                  While sy In [proceduresy,functionsy] Do
                    procdeclaration;
                  test([beginsy],blockbegsys+statbegsys,erkey)
                Until sy In statbegsys;
                tab[prt].adr := lc;
                insymbol;
                statement([semicolon,endsy]+fsys);
                While sy In [semicolon]+statbegsys Do
                  Begin
                    If sy = semicolon Then insymbol
                    Else error(erpun);
                    statement([semicolon,endsy]+fsys)
                  End;
                If sy = endsy Then insymbol
                Else error(erkey);
                test(fsys+[period],[],erkey)
              End;
(* block *)
(*$I cpsint.pas *)
              82
(* ------------------------------------------- MAIN -------*)
              Begin
(* main *)
                ClrScr;
                AssignCrt( Screen );
                rewrite( Screen );
                AssignCrt( Keys );
                reset( Keys );
                CheckEOF := true;
                Assign( input, '' );
                reset( input );
                Assign( output, '' );
                rewrite( output );
                write( '------- CONCURRENT PASCAL-S BY BEN-ARI -------- ' );
                DateAndTime;
                writeln( Screen );
                write( Screen,
                      'Do you want to see the MACHINE CODE generated for this program? ');
                readln( Keys, c );
                If (c = 'y') Or (c = 'Y') Then CODELIST := true
                Else CODELIST := false;
                write( Screen,
                      'Do you want to see a TRACE of the execution of this program? ' );
                readln( Keys, c );
                If (c = 'y') Or (c = 'Y') Then TRACE := true
                Else TRACE := false;
                write( Screen,
                      'Do you want to see EXTRA INTERNAL INFORMATION to aid in debugging? ');
                readln( Keys, c );
                If (c = 'y') Or (c = 'Y') Then ShowInternal := true
                Else ShowInternal := false;
                write( Screen,
                      'Do you want to limit the RUNTIME EXECUTION GRAPH to 2 pages? ' );
                readln( Keys, c );
                If (c = 'y') Or (c = 'Y') Then Adaptive := true
                Else Adaptive := false;
                writeln( Screen );
                writeln( 'USER PROGRAM:' );
                key[ 1] := 'and ';
                key[ 2] := 'array ';
                key[ 3] := 'begin ';
                key[ 4] := 'cobegin ';
                key[ 5] := 'coend ';
                key[ 6] := 'const ';
                key[ 7] := 'div ';
                key[ 8] := 'do ';
                key[ 9] := 'else ';
                key[10] := 'end ';
                key[11] := 'for ';
                key[12] := 'function ';
                key[13] := 'if ';
                key[14] := 'mod ';
                key[15] := 'not ';
                key[16] := 'of ';
                key[17] := 'or ';
                key[18] := 'procedure ';
                key[19] := 'program ';
                key[20] := 'repeat ';
                key[21] := 'select ';
                key[22] := 'then ';
                key[23] := 'to ';
                key[24] := 'type ';
                key[25] := 'until ';
                key[26] := 'var ';
                key[27] := 'while ';
                ksy[ 1] := andsy;
                ksy[ 2] := arraysy;
                ksy[ 3] := beginsy;
                ksy[ 4] := cobegsy;
                ksy[ 5] := coendsy;
                ksy[ 6] := constsy;
                ksy[ 7] := idiv;
                ksy[ 8] := dosy;
                ksy[ 9] := elsesy;
                ksy[10] := endsy;
                ksy[11] := forsy;
                ksy[12] := functionsy;
                ksy[13] := ifsy;
                ksy[14] := imod;
                ksy[15] := notsy;
                ksy[16] := ofsy;
                ksy[17] := orsy;
                ksy[18] := proceduresy;
                ksy[19] := programsy;
                ksy[20] := repeatsy;
                83
                ksy[21] := selectsy;
                ksy[22] := thensy;
                ksy[23] := tosy;
                ksy[24] := typesy;
                ksy[25] := untilsy;
                ksy[26] := varsy;
                ksy[27] := whilesy;
                sps['+'] := plus;
                sps['#'] := pound;
                sps['('] := lparent;
                sps[')'] := rparent;
                sps['='] := eql;
                sps[','] := comma;
                sps['['] := lbrack;
                sps[']'] := rbrack;
                sps['"'] := neq;
                sps['&'] := ampersand;
                sps[';'] := semicolon;
                sps['*'] := times;
                sps['|'] := bar;
                constbegsys := [plus,minus,intcon,charcon,ident];
                typebegsys := [ident,arraysy];
                blockbegsys := [constsy,typesy,varsy,proceduresy,
                               functionsy,beginsy,cobegsy];
                facbegsys := [intcon,charcon,ident,lparent,notsy];
                statbegsys := [beginsy,cobegsy,ifsy,selectsy,
                              whilesy,repeatsy,forsy];
                stantyps := [notyp,ints,bools,chars,semas,chans];
                parseguard := false;
                lc := 0;
                ll := 0;
                cc := 0;
                ch := ' ';
                errpos := 0;
                errs := [];
                insymbol;
                t := -1;
                a := 0;
                b := 1;
                sx := 0;
                c2 := 0;
                display[0] := 1;
                skipflag := false;
                If sy <> programsy Then error(erkey)
                Else
                  Begin
                    insymbol;
                    If sy <> ident Then error(erid)
                    Else
                      Begin
                        progname := id;
                        insymbol
                      End
                  End;
                enter( ' ', variable,notyp,0);
(* sentinel *)
                enter( 'false ', konstant,bools,0);
                enter( 'true ', konstant,bools,1);
                enter( 'char ', type1,chars,1);
                enter( 'boolean ', type1,bools,1);
                enter( 'integer ', type1,ints,1);
                enter( 'semaphore ', type1,semas,2);
                enter( 'channel ', type1,chans,3);
                enter( 'eof ', funktion,bools,17);
                enter( 'eoln ', funktion,bools,18);
                enter( 'read ', prozedure,notyp,1);
                enter( 'readln ', prozedure,notyp,2);
                enter( 'write ', prozedure,notyp,3);
                enter( 'writeln ', prozedure,notyp,4);
                enter( 'wait ', prozedure,notyp,5);
                enter( 'signal ', prozedure,notyp,6);
                enter( 'halt ', prozedure,notyp,7);
                enter( 'abort ', prozedure,notyp,8);
                enter( 'getchannel', prozedure,notyp,9);
                enter( 'send ', prozedure,notyp,10);
                enter( 'receive ', prozedure,notyp,11);
                enter( ' ', prozedure,notyp,0);
(* ??? *)
                With btab[1] Do
                  Begin
                    84
                    last := t;
                    lastpar := 1;
                    psize := 0;
                    vsize := 0
                  End;
                block( blockbegsys+statbegsys, false, 1 );
                If sy <> period Then error(erpun);
                If btab[2].vsize > mainsize Then error(erln);
                emit(31);
(* halt *)
                If Not eof(input) Then readln( input );
                If errs=[] Then
                  Begin
                    If DEBUG Then
                      DumpGlobalNames;
                    If CODELIST Then (* print code *)
                      Begin
                        writeln;
                        writeln( 'CODE:' );
                        For k := 0 To lc-1 Do
                          With code[k] Do
                            writeln( k:5, ') ', f:4, x:10, y:10 );
                        writeln
                      End;
                    writeln;
                    write( '------------- INTERPRET ' );
                    If WAKESEM Then write( 'with semaphore wakeup.' );
                    writeln;
                    interpret
                  End
                Else errormsg;
                Close( Screen );
                Close( Keys )
              End.
              85
              Appendix H
              Concurrent Pascal-S Source Listing
              File 2: CPSLEX.PAS
(* CPSLEX.PAS *)
                      Procedure errormsg;

              Var k : er;
                msg : array[er] Of alfa;
              Begin
                msg[erid] := 'identifier';
                msg[ertyp] := 'type ';
                msg[erkey] := 'keyword ';
                msg[erpun] := 'punctuatio';
                msg[erpar] := 'parameter ';
                msg[ernf] := 'not found ';
                msg[erdup] := 'duplicate ';
                msg[erch] := 'character ';
                msg[ersh] := 'too short ';
                msg[erln] := 'too long ';
                writeln( 'compilation errors' );
                writeln;
                writeln( 'keywords' );
                For k := erid To erln Do
                  If k In errs Then
                    writeln( ord(k), ' ', msg[k] )
              End;
(* errormsg *)
              Procedure endskip;
              Begin
(* underline skipped part of input *)
                While errpos < cc Do
                  Begin
                    write( '_' );
                    errpos := errpos+1
                  End;
                skipflag := false
              End;
(* endskip *)
              Procedure error( n : er );
              Begin
                If errpos = 0 Then write( ' ****' );
                If cc > errpos Then
                  Begin
                    write( ' ': cc-errpos, '''', ord(n): 2 );
                    errpos := cc+3;
                    errs := errs+[n]
                  End
              End;
(* error *)
              Procedure nextch;
(* read ch; process line end *)
              Begin
                If cc = ll Then
                  Begin
                    If ll = llng Then error(erln);
                    If eof(input) Then
                      Begin
                        writeln;
                        writeln( 'program incomplete');
                        errormsg;
                        halt
                      End;
                    If errpos <> 0 Then
                      Begin
                        If skipflag Then endskip;
                        writeln;
                        errpos := 0
                      End;
                    write( lc:5, ' ' );
                    ll := 0;
                    cc := 0;
                    While (Not eoln(input)) And (ll < llng-2) Do
                      Begin
                        ll := ll+1;
                        read(input,ch);
                        write(ch);
                        line[ll] := ch
                      End;
                    writeln;
                    ll := ll+1;
                    line[ll] := ' ';
                    If Not eoln(input) Then
                      Begin
                        ll := ll+1;
                        line[ll] := ' '
                      End;
(* to force error *)
                    86
                    readln( input )
                  End;
                cc := cc+1;
                ch := line[cc]
              End;
(* nextch *)
              Procedure fatal( n : integer );

              Var msg : array[1..6] Of alfa;
              Begin
                writeln;
                errormsg;
                msg[1] := 'identifier';
                msg[2] := 'procedures';
                msg[3] := 'strings ';
                msg[4] := 'arrays ';
                msg[5] := 'levels ';
                msg[6] := 'code ';
                writeln( ' compiler table for ', msg[n], ' is too small');
                halt
              End;
(* fatal *)
(* --------------------------------------------------- INSYMBOL ---- *)
              Procedure insymbol;
(* reads next symbol *)

              Label 1,2,3;

              Var i, j, k, e : integer;
              Begin
                1: While ch = ' ' Do
                     nextch;
                Case ch Of 
                  'A' .. 'Z', 'a' .. 'z' :
                                           Begin
(* ident or wordsymbol *)
                                             k := 0;
                                             id := ' ';
                                             Repeat
                                               If k < alng Then
                                                 Begin
                                                   k := k+1;
                                                   id[k] := ch
                                                 End;
                                               nextch
                                             Until Not ( ch In ['A'..'Z','a'..'z','0'..'9'] );
                                             i := 1;
                                             j := nkw;
(* binary search *)
                                             Repeat
                                               k := (i+j) Div 2;
                                               If id <= key[k] Then j := k-1;
                                               If id >= key[k] Then i := k+1
                                             Until i > j;
                                             If i-1 > j Then sy := ksy[k]
                                             Else sy := ident
                                           End;
                  '0' .. '9' :
                               Begin
(* number *)
                                 k := 0;
                                 inum := 0;
                                 sy := intcon;
                                 Repeat
                                   inum := inum*10 + ord(ch)-ord('0');
                                   k := k+1;
                                   nextch
                                 Until Not ( ch In ['0'..'9'] );
                                 If (k > kmax) Or (inum > nmax) Then
                                   Begin
                                     error(erln);
                                     inum := 0;
                                     k := 0
                                   End
                               End;
                  ':' :
                        Begin
                          nextch;
                          If ch = '=' Then
                            Begin
                              sy := becomes;
                              nextch
                            End
                          Else sy := colon
                        End;
                  '-' :
                        Begin
                          nextch;
                          If ch = '>' Then
                            87
                            Begin
                              sy := arrow;
                              nextch
                            End
                          Else sy := minus
                        End;
                  '<' :
                        Begin
                          nextch;
                          If ch = '=' Then
                            Begin
                              sy := leq;
                              nextch
                            End
                          Else If ch = '>' Then
                                 Begin
                                   sy := neq;
                                   nextch
                                 End
                          Else sy := lss
                        End;
                  '>' :
                        Begin
                          nextch;
                          If ch = '=' Then
                            Begin
                              sy := geq;
                              nextch
                            End
                          Else sy := gtr
                        End;
                  '.' :
                        Begin
                          nextch;
                          If ch = '.' Then
                            Begin
                              sy := colon;
                              nextch
                            End
                          Else sy := period
                        End;
                  '''' : (* strings *)
                         Begin
                           k := 0;
                           2: nextch;
                           If ch = '''' Then
                             Begin
                               nextch;
                               If ch <> '''' Then goto 3
                             End;
                           If sx+k = smax Then fatal(3);
                           stab[sx+k] := ch;
                           k := k+1;
                           If cc = 1 Then
                             Begin
(* end line *)                 k := 0
                             End
                           Else goto 2;
                           3: If k = 1 Then
                                Begin
                                  sy := charcon;
                                  inum := ord(stab[sx])
                                End
                              Else If k = 0 Then
                                     Begin
                                       error(ersh);
                                       sy := charcon;
                                       inum := 0
                                     End
                              Else
                                Begin
                                  sy := stringsy;
                                  inum := sx;
                                  sleng := k;
                                  sx := sx+k
                                End
                         End;
                  '(' :
                        Begin
(* possible comment *)
                          nextch;
                          If ch <> '*' Then sy := lparent
                          Else
                            Begin
(* comment *)
                              Repeat
                                While ch <> '*' Do
                                  nextch;
                                nextch
                              Until ch = ')';
                              nextch;
                              goto 1
                            End
                        End;
                  88
                  '+', '&', '*', ')', '=', ',', '[', ']', ';', '|', '#' :
                                                                          Begin
                                                                            sy := sps[ch];
                                                                            nextch
                                                                          End;
                  Else
                    Begin
                      error(erch);
                      nextch;
                      goto 1
                    End
                End
              End;
(* insymbol *)
(* -------------------------------------------------- ENTER --- *)
              Procedure enter( x0 : alfa; x1 : Object; x2 : types; x3 : integer );
              Begin
(* standard identifier *)
                t := t+1;
                With tab[t] Do
                  Begin
                    name := x0;
                    link := t-1;
                    obj := x1;
                    typ := x2;
                    ref := 0;
                    normal := true;
                    lev := 0;
                    adr := x3
                  End
              End;
(* enter *)
              Procedure enterarray( tp : types; l,h : integer );
              Begin
                If l > h Then error(ertyp);
                If (abs(l)>xmax) Or (abs(h)>xmax) Then
                  Begin
                    error(ertyp);
                    l := 0;
                    h := 0
                  End;
                If a = amax Then fatal(4)
                Else
                  Begin
                    a := a+1;
                    With atab[a] Do
                      Begin
                        inxtyp := tp;
                        low := l;
                        high := h
                      End
                  End
              End;
(* enterarray *)
              Procedure enterblock;
              Begin
                If b = bmax Then fatal(2)
                Else
                  Begin
                    b := b+1;
                    btab[b].last := 0;
                    btab[b].lastpar := 0
                  End
              End;
(* enterblock *)
              Procedure emit( fct : integer );
              Begin
                If lc = cmax Then fatal(6);
                With code[lc] Do
                  Begin
                    f := fct;
                    x := 0;
                    y := 0
                  End;
                lc := lc+1
              End;
(* emit *)
              Procedure emit1( fct,b : integer );
              Begin
                If lc =cmax Then fatal(6);
                With code[lc] Do
                  Begin
                    f := fct;
                    x := 0;
                    y := b
                  End;
                lc := lc+1
              End;
(* emit1 *)
              Procedure emit2( fct,a,b : integer );
              89
              Begin
                If lc = cmax Then fatal(6);
                With code[lc] Do
                  Begin
                    f := fct;
                    x := a;
                    y := b
                  End;
                lc := lc+1
              End;
(* emit2 *)
              90
              Appendix I
              Concurrent Pascal-S Source Listing
              File 3: CPSINT.PAS
(* ----------- CPSINT.PAS ------------ *)
                      Procedure interpret;

              Const 
(* status of a process block *)
                free = 0;
                running = 1;
                ready = 2;
                semablock = 3;
                sendblock = 4;
                recblock = 5;
                selblock = 6;
                sleeping = 7;
                nilproc = -1;
(* nil pointer for ptype references *)
                main = 0;
(* index of main process *)
                mainquant = 10000;
(* quantum for main process *)
                tru = 1;
(* integer value of true *)
                fals = 0;
(* integer value of false *)
                charl = 32;
(* lowest print character ordinal *)
                charh = 126;
(* highest print character ordinal *)
                procmax = 200;
(* maximum number of processes *)
                sentinel = 0;
(* for communication statements *)

              Type 
                ptype = nilproc .. pmax;
(* index over processors *)
                proctype = 0 .. procmax;
                waitptr = ^waitnode;
                waitnode = Record
                  wait, signal : integer;
                  next : waitptr
                End;
                qptr = ^qentry;
                qentry = Record
                  process : main .. pmax;
                  channel : integer;
                  direction : send .. purebool;
                  comm : integer;
(* expression or var address *)
                  resume : integer;
(* resumption address *)
                  next,
                  setlink : qptr (* circular set of comm requests *)
                End;

              Var 
                ir : order;
(* instruction buffer *)
                ps : (* processor status *)
                     ( run, timeout, sleep, suspended, kill, wakeup,
                      fin, divchk, inxchk, stkchk, procchk, guardchk,
                      linchk, lngchk, redchk, chanchk, deadlock, abort );
                lncnt, (* number of lines *)
                chrcnt : integer;
(* number of characters in line *)
                h1, h2, h3, h4 : integer;
(* local variables *)
                s : array[1..stmax] Of integer;
(* the stack *)
                numforks : integer;
(* number of forks performed during program execution *)
                selcount : integer;
(* no. of communications in select statement *)
                setptr : qptr;
(* circular set of comm requests *)
(* processor table --- one entry for each processor *)
                ptab : array[0..pmax] Of 
                       Record
(* process descriptor *)
                         procno : proctype;
(* unique process identifier *)
                         parent : ptype;
                         91
                         childcount : integer;
                         status : free .. sleeping;
                         blocker : integer;
(* index of semaphore *)
                         nextp : ptype;
                         t, b, (* top, bottom of stack *)
                         pc, (* program counter *)
                         stacklimit : integer;
                         display : array[1..lmax] Of integer;
                         tstart : integer;
(* time process began *)
                         timer : integer;
(* no. of instructions executed *)
                         tblocked : integer;
(* time process blocked on last wait *)
                         totalwait : integer (* total time spent waiting *)
                       End;
                freetop : ptype;
(* top of free blocks list *)
                lastready : ptype;
(* circular ready process queue *)
                lastpr, (* previous running process *)
                relpr, (* released process to be waked up *)
                childpr, (* newly forked child process *)
                runpr : ptype;
(* current running process *)
                stepcount : integer;
(* number of steps before timeout *)
                seed : integer;
(* random seed *)
                lock : boolean;
(* to suppress timeouts *)
                stkincr, (* stacksize per process *)
                Indent : integer;
(* for trace printouts per process *)
                inserted : boolean;
(* to re-insert a process into Ready Q *)
                before, after : ptype;
(* pointers into Ready Q *)
                clock, (* clock of process to be inserted *)
                afterclock : integer;
(* clock of process pointed to by after *)
                serviced : boolean;
(* to find a serviceable comm request *)
                last, tmpptr : qptr;
(* summary table of processes *)
                sumtab : array[proctype] Of 
                         Record
                           processor_used : 0 .. pmax;
                           start,
                           running,
                           waiting : integer;
                           waitlist : waitptr
                         End;
                proccount : proctype;
(* index to sumtab *)
(* channel table *)
                chantab : array[1..tmax] Of 
                          Record
                            owner : ptype;
                            uniqueowner : nilproc .. procmax;
                            sendcount : integer;
                            sendq,
                            receiveq : qptr
                          End;
              Procedure RuntimeSummary;

              Var i : integer;
                runsum, waitsum, elapsum : longint;
              Begin
                runsum := 0;
                waitsum := 0;
                elapsum := 0;
                writeln;
                writeln( 'RUNTIME SUMMARY:' );
                writeln;
                writeln( 'Process# /' );
                92
                write ( 'Processor used Start Run time Time waiting ' );
                writeln( 'Finish Elapsed time' );
                For i := 0 To proccount Do
                  With sumtab[i] Do
                    Begin
                      writeln( i:5, '/':3, processor_used:4, start:10, running:10,
                              waiting:14, start+running+waiting:13, running+waiting:12 );
                      runsum := runsum + running;
                      waitsum := waitsum + waiting;
                      elapsum := elapsum + running + waiting
                    End;
                writeln( '--------------', '----':18, '----':14, '----':25 );
                writeln( 'TOTALS:', runsum:25, waitsum:14, elapsum:25 )
              End;
(* RuntimeSummary *)
              Procedure RelUtilization;

              Var i : integer;
                runsum, waitsum : longint;
              Begin
                runsum := 0;
                waitsum := 0;
                writeln;
                writeln;
                writeln( 'RELATIVE UTILIZATION PERCENTAGES (across processes):' );
                writeln;
                writeln( 'Process# Run/ Run+Wait = Utilization' );
                For i := 0 To proccount Do
                  With sumtab[i] Do
                    Begin
                      writeln( i:5, running:10, '/', running:4, '+', waiting:4, '=':3,
                              running/(running+waiting)*100: 9: 1, '%' );
                      runsum := runsum + running;
                      waitsum := waitsum + waiting
                    End;
                writeln( '--------', '--------------':17, '------':13 );
                writeln( 'TOTALS:', runsum:8, '/', runsum:4, '+', waitsum:4, '=':3,
                        runsum/(runsum+waitsum)*100: 9: 1, '%' );
                writeln;
                writeln( 'GRANULARITY of this application =' );
                writeln( 'ratio of concurrency overhead to actual work being performed =' );
                write ( numforks * 5, ' / ', runsum, ' = ' );
                writeln( numforks * 5 / runsum * 100 :5:1, '%' );
                writeln( '(High percentage = Fine-grained; Low percentage = Coarse-grained)')
              End;
(* RelUtilization *)
              Procedure AbsUtilization;

              Var used : set Of 0..pmax;
                curproc, run, wait, idle, last, i, no_procs : longint;
                runsum, waitsum, idlesum, checksum : longint;
                AbsUtilTab : array[0..pmax] Of 
                             Record
                               R, W, I : longint
                             End;
              Procedure BarChart;

              Var count, len, j, k : integer;
                ratio, rlen : real;
              Begin
                ratio := 70 / (sumtab[main].start+sumtab[main].running+
                         sumtab[main].waiting);
                writeln;
                writeln( 'Processor Utilization Graph' );
                For j := 0 To no_procs Do
                  Begin
                    93
                    count := 0;
                    write( j:5, ' ':5 );
                    rlen := AbsUtilTab[j].R * ratio;
                    If (rlen < 1) And (rlen > 0) Then rlen := 1;
                    len := round( rlen );
                    For k := 1 To len Do
                      Begin
                        count := count + 1;
                        If count <= 70 Then write( chr(219) ) (* Run *)
                      End;
                    rlen := AbsUtilTab[j].W * ratio;
                    If (rlen < 1) And (rlen > 0) Then rlen := 1;
                    len := round( rlen );
                    For k := 1 To len Do
                      Begin
                        count := count + 1;
                        If count <= 70 Then write( chr(177) ) (* Wait *)
                      End;
                    For k := count+1 To 70 Do
                      write( '-' );
(* Idle *)
                    writeln;
                    writeln
                  End;
                writeln( ' ':10, chr(219), chr(219), chr(219), chr(219), chr(219),
                ' = Run', ' ': 17, chr(177), chr(177), chr(177), chr(177),
                               chr(177), ' = Wait', ' ': 17, '----- = Idle' )
              End;
(* BarChart *)
              Begin
                no_procs := -1;
                runsum := 0;
                waitsum := 0;
                idlesum := 0;
                used := [];
                writeln;
                writeln;
                writeln( 'ABSOLUTE UTILIZATION PERCENTAGES & GRAPHS (across processors):' );
                writeln;
                writeln( 'Processor Run+Wait/ Run+Wait+Idle = Utilization' );
                For curproc := 0 To proccount Do
                  If Not (sumtab[curproc].processor_used In used) Then
                    Begin
                      run := 0;
                      wait := 0;
                      idle := 0;
                      used := used + [sumtab[curproc].processor_used];
                      For i := curproc To proccount Do
                        If sumtab[i].processor_used = sumtab[curproc].processor_used Then
                          Begin
                            If run = 0 Then
                              idle := idle + sumtab[i].start
                            Else
                              idle := idle + sumtab[i].start - (sumtab[last].start +
                                      sumtab[last].running + sumtab[last].waiting);
                            last := i;
                            run := run + sumtab[i].running;
                            wait := wait + sumtab[i].waiting
                          End;
                      idle := idle + sumtab[main].start + sumtab[main].running +
                              sumtab[main].waiting - (sumtab[last].start +
                              sumtab[last].running + sumtab[last].waiting);
                      writeln( sumtab[curproc].processor_used:5, run:11, '+', wait:4, '/',
                              run:4, '+', wait:4, '+', idle:4, '=':3,
                              (run+wait)/(run+wait+idle)*100: 9: 1, '%' );
                      94
                      With AbsUtilTab[sumtab[curproc].processor_used] Do
                        Begin
                          R := run;
                          W := wait;
                          I := idle
                        End;
                      no_procs := no_procs + 1;
                      runsum := runsum + run;
                      waitsum := waitsum + wait;
                      idlesum := idlesum + idle
                    End;
                writeln( '---------', '------------------------':27, '------':13 );
                writeln( 'TOTALS:', runsum:9, '+', waitsum:4, '/', runsum:4, '+', waitsum:4,
                        '+', idlesum:4, '=':3,
                        (runsum+waitsum)/(runsum+waitsum+idlesum)*100: 9: 1, '%' );
                checksum := sumtab[main].start + sumtab[main].running + sumtab[main].waiting;
                For i := 0 To no_procs Do
(* consistency check *)
                  If (AbsUtilTab[i].R+AbsUtilTab[i].W+AbsUtilTab[i].I) <> checksum Then
                    writeln( '-- Error in consistency of Run, Wait, & Idle times for ',
                            'processor ', i, ' --' );
                BarChart
              End;
(* AbsUtilization *)
              Procedure DisplayGraph;

              Var time, endofprog, spaces, dashes, x : integer;
                displayincr : integer;
(* time increment for graph display *)
                slotempty : boolean;
                process : proctype;
                processor : 0 .. pmax;
                ptr : waitptr;
              Begin
                writeln;
                writeln;
                endofprog := sumtab[main].start+sumtab[main].running+sumtab[main].waiting;
                time := 0;
                If ((endofprog+1) > 132) And Adaptive Then
                  displayincr := (endofprog+1) Div 100
                Else
                  displayincr := 1;
                writeln( 'RUNTIME GRAPH:' );
                write( '---- ' );
                spaces := pmax * 5 + 1;
                If pmax > 9 Then
                  spaces := spaces + pmax - 9;
                dashes := spaces - 12;
                For x := 1 To (dashes Div 2) Do
                  write( '-' );
                write( ' Processors ' );
                For x := 1 To (dashes Div 2) Do
                  write( '-' );
                If ((dashes Div 2) * 2) <> dashes Then
                  write( '-' );
                writeln;
                write( 'Time' );
                For processor := 0 To pmax Do
                  write( ' ', processor );
                writeln;
                write( '---- -' );
                For processor := 1 To pmax Do
                  Begin
                    write( '-----' );
                    If processor > 9 Then write( '-' )
                  End;
                95
                writeln;
                While time < endofprog Do
                  Begin
                    write( time:4 );
                    For processor := 0 To pmax Do
                      Begin
                        slotempty := true;
                        process := 0;
                        While slotempty Do
                          Begin
                            If (sumtab[process].processor_used = processor) And
                               (sumtab[process].start <= time) And
                               (time < (sumtab[process].start+sumtab[process].running+
                               sumtab[process].waiting)) Then
                              Begin
                                ptr := sumtab[process].waitlist;
                                While (ptr <> Nil) And slotempty Do
                                  If (ptr^.wait <= time) And
                                     (time < ptr^.signal) Then
                                    Begin
                                      write( '.':5 );
                                      slotempty := false
                                    End
                                  Else
                                    ptr := ptr^.next;
                                If slotempty Then
                                  Begin
                                    write( process:5 );
                                    slotempty := false
                                  End
                              End
                            Else
                              Begin
                                process := process + 1;
                                If process > proccount Then
                                  Begin
                                    write( ' ':5 );
                                    slotempty := false
                                  End
                              End
                          End
                      End;
                    time := time + displayincr;
                    writeln
                  End;
                write( endofprog:4 );
                If ps <> fin Then writeln( 'HALT':(runpr*(Indent+1)+Indent+4) )
                Else writeln
              End;
(* DisplayGraph *)
              Procedure AddWait( id : ptype; time : integer );

              Var ptr : waitptr;
              Begin
                ptr := sumtab[ptab[id].procno].waitlist;
                If ptr = Nil Then
                  Begin
                    new( sumtab[ptab[id].procno].waitlist );
                    sumtab[ptab[id].procno].waitlist^.wait := time;
                    sumtab[ptab[id].procno].waitlist^.next := Nil
                  End
                Else
                  96
                  Begin
                    While ptr^.next <> Nil Do
                      ptr := ptr^.next;
                    new( ptr^.next );
                    ptr^.next^.wait := time;
                    ptr^.next^.next := Nil
                  End
              End;
(* AddWait *)
              Procedure AddSignal( id : ptype; time : integer );

              Var ptr : waitptr;
              Begin
                ptr := sumtab[ptab[id].procno].waitlist;
                While ptr^.next <> Nil Do
                  ptr := ptr^.next;
                ptr^.signal := time
              End;
(* AddSignal *)
              Procedure DumpWaitlist;

              Var ptr : waitptr;
                i : integer;
              Begin
                writeln;
                writeln( 'Dump Waitlist:' );
                For i := 0 To proccount Do
                  Begin
                    write( i:2, ') ' );
                    ptr := sumtab[i].waitlist;
                    If ptr = Nil Then write( 'No waits.' )
                    Else
                      While ptr <> Nil Do
                        Begin
                          write( ptr^.wait, ' & ', ptr^.signal );
                          ptr := ptr^.next;
                          If ptr <> Nil Then write( ' / ' )
                        End;
                    writeln
                  End
              End;
(* DumpWaitlist *)
              Procedure DumpSumtab;

              Var i : integer;
              Begin
                writeln;
                writeln( 'Dump Sumtab:' );
                For i := 0 To proccount Do
                  With sumtab[i] Do
                    writeln( 'sumtab[', i:2, '] processor_used=', processor_used:3,
                            ' start=', start:4, ' running=', running:4,
                            ' waiting=', waiting:4 )
              End;
(* DumpSumtab *)
              Procedure AddReady( new : ptype );
(* assumes non-empty Ready Q *)

              Var follow : ptype;
              Begin
                follow := ptab[lastready].nextp;
                ptab[lastready].nextp := new;
                With ptab[new] Do
                  Begin
                    nextp := follow;
                    97
                    status := ready;
                    blocker := 0
                  End;
                lastready := new
              End;
(* AddReady *)
              Procedure RemoveReady;
              Begin
                If lastready = runpr Then
                  lastready := nilproc (* now empty *)
                Else
                  ptab[lastready].nextp := ptab[runpr].nextp
              End;
(* RemoveReady *)
              Procedure Suspend( sema : integer );

              Var lastw, follow : ptype;
              Begin
                With ptab[runpr] Do
                  Begin
                    status := semablock;
                    blocker := sema;
                    tblocked := tstart + timer + totalwait;
                    AddWait( runpr, tblocked )
                  End;
                lastw := s[sema+1];
                If lastw = nilproc Then
                  ptab[runpr].nextp := runpr
                Else
                  Begin
                    follow := ptab[lastw].nextp;
                    ptab[lastw].nextp := runpr;
                    ptab[runpr].nextp := follow
                  End;
                s[sema+1] := runpr;
              End;
(* Suspend *)
              Procedure Release( sema : integer );
(* assuming someone waits *)

              Var lastw : ptype;
                time : integer;
              Begin
                lastw := s[sema+1];
                relpr := ptab[lastw].nextp;
                If relpr = lastw Then
                  s[sema+1] := nilproc
                Else
                  ptab[lastw].nextp := 
                                       ptab[relpr].nextp;
                With ptab[relpr] Do
                  Begin
                    time := ptab[runpr].tstart + ptab[runpr].timer + ptab[runpr].totalwait;
                    tblocked := time - tblocked;
                    totalwait := totalwait + tblocked
                  End;
(* with *)
                AddSignal( relpr, time )
              End;
(* Release *)
              Procedure EnQueue( tos, reqno : integer; Var last : qptr; base : boolean );

              Var ptr, delptr : qptr;
              Procedure FillNode( node : qptr; Var last : qptr );
              Begin
                With node^ Do
                  Begin
                    98
                    direction := s[tos];
                    process := s[tos-2];
                    channel := s[tos-3];
                    comm := s[tos-4];
                    resume := s[tos-1];
                    next := Nil;
                    With ptab[process] Do
                      Begin
                        If reqno = 1 Then
                          Begin
                            setptr := node;
                            setlink := node;
                            last := node
                          End
                        Else If base Then
                               Begin
                                 last^.setlink := node;
                                 setlink := setptr
                               End
                        Else
                          Begin
                            last^.setlink := node;
                            last := node
                          End
                      End
                  End
              End;
(* FillNode *)
              Begin
(* EnQueue *)
                If s[tos] = send Then
                  Begin
                    While chantab[s[tos-3]].sendq^.channel = -1 Do
                      Begin
                        delptr := chantab[s[tos-3]].sendq;
                        With chantab[s[tos-3]] Do
                          sendq := sendq^.next;
                        delptr^.next := Nil;
                        dispose( delptr )
                      End;
                    With chantab[s[tos-3]] Do
                      Begin
                        ptr := sendq;
                        sendcount := sendcount + 1
                      End
                  End
                Else If s[tos] = receive Then
                       ptr := chantab[s[tos-3]].receiveq
                Else (* pure Boolean *)
                  new( ptr );
                If s[tos] = purebool Then
                  FillNode( ptr, last )
                Else If ptr = Nil Then
                       Begin
                         new( ptr );
                         If s[tos] = send Then
                           chantab[s[tos-3]].sendq := ptr
                         Else (* receive *)
                           chantab[s[tos-3]].receiveq := ptr;
                         FillNode( ptr, last )
                       End
                Else
                  Begin
                    While ptr^.next <> Nil Do
                      ptr := ptr^.next;
                    99
                    new( ptr^.next );
                    FillNode( ptr^.next, last )
                  End
              End;
(* EnQueue *)
              Procedure CancelNodes( dirptr : qptr );

              Var delptr, start : qptr;
                numlinks, x : integer;
              Begin
                numlinks := 0;
                start := dirptr;
                Repeat
                  numlinks := numlinks + 1;
                  dirptr := dirptr^.setlink
                Until dirptr = start;
                For x := 1 To numlinks Do
                  If dirptr^.direction = send Then
                    Begin
                      With chantab[dirptr^.channel] Do
                        sendcount := sendcount - 1;
                      dirptr^.channel := -1;
                      delptr := dirptr;
                      dirptr := dirptr^.setlink;
                      delptr^.setlink := delptr
                    End
                  Else If dirptr^.direction = receive Then
                         Begin
                           delptr := dirptr;
                           dirptr := dirptr^.setlink;
                           chantab[delptr^.channel].receiveq := Nil;
                           dispose( delptr )
                         End
                  Else (* pure Boolean *)
                    Begin
                      delptr := dirptr;
                      dirptr := dirptr^.setlink;
                      dispose( delptr )
                    End
              End;
(* CancelNodes *)
              Procedure Rendezvous( ptr : qptr );

              Var sendptr, recptr : qptr;
                chanid, wakeup1, wakeup2, time : integer;
              Begin
(* Rendezvous *)
                chanid := ptr^.channel;
                sendptr := chantab[chanid].sendq;
                recptr := chantab[chanid].receiveq;
                s[recptr^.comm] := sendptr^.comm;
(* exchange *)
                time := ptab[runpr].tstart + ptab[runpr].timer + ptab[runpr].totalwait;
                wakeup1 := sendptr^.process;
                wakeup2 := recptr^.process;
                If (ptab[wakeup1].status <> ready) And (ptab[wakeup1].status <> running) Then
                  Begin
                    AddReady( wakeup1 );
                    With ptab[wakeup1] Do
                      Begin
                        tblocked := time - tblocked;
                        totalwait := totalwait + tblocked
                      End;
                    AddSignal( wakeup1, time )
                  End;
                100
                ptab[wakeup1].pc := sendptr^.resume;
                If (ptab[wakeup2].status <> ready) And (ptab[wakeup2].status <> running) Then
                  Begin
                    AddReady( wakeup2 );
                    With ptab[wakeup2] Do
                      Begin
                        tblocked := time - tblocked;
                        totalwait := totalwait + tblocked
                      End;
                    AddSignal( wakeup2, time )
                  End;
                ptab[wakeup2].pc := recptr^.resume;
                CancelNodes( sendptr );
                CancelNodes( recptr )
              End;
(* Rendezvous *)
              Procedure WaitforRen( dir, ch : integer );
(* Wait for Rendezvous *)
              Begin
                RemoveReady;
                With ptab[runpr] Do
                  Begin
                    Case dir Of 
                      send : status := sendblock;
                      receive : status := recblock;
                      select : status := selblock
                    End;
                    blocker := ch;
                    tblocked := tstart + timer + totalwait;
                    AddWait( runpr, tblocked )
                  End;
                ps := suspended
              End;
(* WaitforRen *)
              Procedure ReportProcess( id : ptype );
(* retain vital information of each process before *)
(* returning its process block to the free list *)
              Begin
                With sumtab[ptab[id].procno] Do
                  Begin
                    processor_used := id;
                    start := ptab[id].tstart;
                    running := ptab[id].timer;
                    waiting := ptab[id].totalwait
                  End
              End;
(* ReportProcess *)
              Procedure nextproc;
(* schedule next running process via round-robin *)
              Begin
(* circular shift of ready queue *)
                lastready := ptab[lastready].nextp;
              End;
(* nextproc *)
              Procedure setquantum;
              Begin
                If runpr = main Then stepcount := mainquant
                Else stepcount := quantmin + trunc(random*quantwidth)
              End;
(* setquantum *)
(* functions to convert integers to booleans and conversely *)
              101
              Function itob(i : integer) : boolean;
              Begin
                itob := ( i = tru )
              End;
              Function btoi( b : boolean ) : integer;
              Begin
                If b Then btoi := tru
                Else btoi := fals
              End;
              Procedure PostMortemDump;

              Var i, tt : integer;
                ptr : qptr;
              Begin
                writeln;
                writeln;
                With ptab[runpr] Do
                  write( 'Halt at ', pc, ' in process ', runpr, ' because of ' );
                Case ps Of 
                  deadlock : writeln( 'deadlock' );
                  guardchk : writeln( 'false guards in select statement' );
                  divchk : writeln( 'division by zero' );
                  inxchk : writeln( 'invalid index' );
                  stkchk : writeln( 'storage overflow' );
                  linchk : writeln( 'too much output' );
                  lngchk : writeln( 'line too long' );
                  redchk : writeln( 'reading past end of file' );
                  procchk: writeln( 'too many process forks' );
                  chanchk: writeln( 'illegal channel access' );
                  abort : writeln( 'programmer abort' )
                End;
                writeln;
                writeln;
                writeln( ' Process Status Blocker PC Run Wait ' );
                For i := 0 To pmax Do
                  With ptab[i] Do
                    If status <> free Then
                      Begin
                        If (status <> running) And (status <> ready) Then
                          Begin
                            tt := ptab[runpr].tstart+ptab[runpr].timer+
                                  ptab[runpr].totalwait;
                            tblocked := tt - tblocked;
                            totalwait := totalwait + tblocked;
                            AddSignal( i, tt )
                          End;
                        ReportProcess( i );
                        writeln;
                        write( procno:4, ') ' );
                        Case status Of 
                          running : write( 'HALT ' );
                          ready : write( 'run ' );
                          semablock : write( 'wait sem ', blocker:2 );
                          sendblock : write( 'send ch ', blocker:2, ' ' );
                          recblock : write( 'receive ch ', blocker:2, ' ' );
                          selblock : write( 'guard ' );
                          sleeping : write( 'sleep sleep ' )
                        End;
                        writeln( pc:7, timer:7, totalwait:8 )
                      End;
                writeln;
                writeln;
                writeln( 'Global Variables:' );
                writeln( 'NAME TYPE OFFSET VALUE COMMENT' );
                writeln( '---- ---- ------ ----- -------' );
                102
                write ( 'FBsema special 5', s[5]:11, ' ':4 );
                If s[6] = -1 Then writeln( 'Free process blocks still available' )
                Else writeln( 'No free block available for pr ', s[6] );
                For i := btab[1].last+1 To tmax Do
                  With tab[i] Do
                    If (lev = 1) And (obj = variable) Then
                      If typ In stantyps Then
                        Case typ Of 
                          ints : writeln( name, ' integer ', adr:4, s[adr]:11 );
                          bools : writeln( name,' boolean ', adr:4,itob(s[adr]): 11);
                          chars : writeln( name, ' character ', adr:4,
                                          chr(s[adr] Mod 256): 11 );
                          semas :
                                  Begin
                                    write(name,' semaphore ',adr:4,s[adr]:11, ' ':4);
                                    If s[adr+1] = -1 Then
                                      writeln( 'Not blocking any process' )
                                    Else writeln( 'Blocking process ', s[adr+1] )
                                  End;
                          chans :
                                  Begin
                                    write( name, ' channel ', adr:4, ' ':15 );
                                    If chantab[i].uniqueowner = nilproc Then
                                      writeln( 'Channel not owned' )
                                    Else
                                      writeln( 'Owner = process ',
                                              chantab[i].uniqueowner );
                                    write( ' ':42 );
                                    If chantab[i].receiveq = Nil Then write( 'No r' )
                                    Else write( 'R' );
                                    writeln( 'eceives are pending' );
                                    write( ' ':42 );
                                    If chantab[i].sendcount = 0 Then
                                      writeln( 'No sent messages are pending' )
                                    Else
                                      Begin
                                        writeln( 'Sent messages pending:' );
                                        ptr := chantab[i].sendq;
                                        While ptr <> Nil Do
                                          Begin
                                            If ptr^.channel <> -1 Then
                                              writeln( ptr^.comm:48,
                                                      ' from process ',
                                                      ptr^.process);
                                            ptr := ptr^.next
                                          End
                                      End
                                  End
                        End
              End;
(* PostMortemDump *)
              Begin
(* interpret *)
                numforks := 0;
                proccount := 0;
                stkincr := (stmax-mainsize) Div pmax;
(* partition the stack *)
                Indent := 50 Div (pmax+1);
(* avoid wrap for tracing *)
(* initialize the main process *)
                s[1] := 0;
                s[2] := 0;
                s[3] := -1;
                s[4] := btab[1].last;
                With ptab[main] Do
(* main process block *)
                  Begin
                    procno := proccount;
(* main process will be 0 *)
                    parent := nilproc;
                    childcount := 0;
                    status := running;
                    blocker := 0;
                    103
                    nextp := nilproc;
                    b := 0;
                    display[1] := 0;
                    t := btab[2].vsize-1;
                    pc := tab[s[4]].adr;
                    stacklimit := mainsize;
                    tstart := 0;
                    timer := 0;
                    tblocked := 0;
                    totalwait := 0
                  End;
(* initialize the free block list *)
                For h1 := 1 To pmax Do
                  With ptab[h1] Do
                    Begin
                      If h1 < pmax Then nextp := h1+1
                      Else nextp := nilproc;
                      status := free;
                      b := ptab[h1-1].stacklimit+1;
                      stacklimit := b+stkincr-1;
                      timer := 0;
                      tblocked := 0;
                      totalwait := 0
                    End;
                freetop := 1;
(* initialize sumtab's waitlist *)
                For h1 := 0 To procmax Do
                  sumtab[h1].waitlist := Nil;
(* initialize channel table *)
                For h1 := 1 To tmax Do
                  With chantab[h1] Do
                    Begin
                      owner := nilproc;
(* no one owns this channel *)
                      uniqueowner := nilproc;
                      sendcount := 0;
                      sendq := Nil;
                      receiveq := Nil
                    End;
(* initialize ready process queue to main alone *)
                lastready := main;
                ptab[main].nextp := main;
                runpr := main;
                If USEQUANTUM Then
                  setquantum
                Else
                  stepcount := 0;
(* initialize FBsema *)
                s[5] := pmax;
                s[6] := nilproc;
                lock := false;
                randomize;
                lncnt := 0;
                chrcnt := 0;
                Repeat
                  ps := run;
                  With ptab[runpr] Do
                    Begin
                      ir := code[pc];
                      pc := pc+1;
                    End;
                  104
                  With ptab[runpr] Do
                    Begin
                      timer := timer + 1;
                      Case ir.f Of 
                        0 :
                            Begin
(* load address *)
                              t := t+1;
                              If t > stacklimit Then ps := stkchk
                              Else s[t] := display[ir.x] + ir.y
                            End;
                        1 :
                            Begin
(* load value *)
                              t := t+1;
                              If t > stacklimit Then ps := stkchk
                              Else s[t] := s[display[ir.x] + ir.y]
                            End;
                        2 :
                            Begin
(* load indirect *)
                              t := t+1;
                              If t > stacklimit Then ps := stkchk
                              Else s[t] := s[s[display[ir.x] + ir.y]]
                            End;
                        3 :
                            Begin
(* update display *)
                              h1 := ir.y;
                              h2 := ir.x;
                              h3 := b;
                              Repeat
                                display[h1] := h3;
                                h1 := h1-1;
                                h3 := s[h3+2]
                              Until h1 = h2
                            End;
                        4 :
                            Begin
(* fork new child process *)
                              numforks := numforks + 1;
                              childpr := freetop;
                              freetop := ptab[freetop].nextp;
                              AddReady( childpr );
                              If TRACE Then
                                writeln( ' ':Indent*runpr,
                                        'FORK ', childpr, ' at ', pc );
                              proccount := proccount + 1;
                              With ptab[childpr] Do
                                Begin
                                  procno := proccount;
                                  parent := runpr;
                                  childcount := 0;
                                  pc := ptab[runpr].pc+1;
(* after TRA *)
                                  t := b-1;
(* inherit parent's environment *)
                                  tstart := ptab[parent].tstart + ptab[parent].timer +
                                            ptab[parent].totalwait;
                                  timer := 0;
                                  tblocked := 0;
                                  totalwait := 0;
                                  For h1 := 1 To ir.y Do
                                    display[h1] := ptab[runpr].display[h1];
                                  ptab[parent].childcount := 
                                                             ptab[parent].childcount+1
                                End
                            End;
                        5 :
                            Begin
(* kill terminates child process *)
                              If TRACE Then
                                writeln( ' ':Indent*runpr,
                                        'KILL ', runpr, ' at ', pc );
                              105
                              ptab[parent].childcount := 
                                                         ptab[parent].childcount-1;
                              If (ptab[parent].childcount = 0) And
                                 (ptab[parent].status = sleeping) Then (* awaken parent *)
                                Begin
                                  ptab[parent].status := ready;
                                  ptab[parent].tblocked := tstart + timer + totalwait -
                                                           ptab[parent].tblocked;
                                  ptab[parent].totalwait := ptab[parent].totalwait +
                                                            ptab[parent].tblocked;
                                  AddSignal( parent, tstart+timer+totalwait );
                                  AddReady( parent )
                                End;
                              RemoveReady;
                              ReportProcess( runpr );
(* signal FBsema *)
                              If TRACE Then
                                writeln(' ':Indent*runpr, 'SIGNAL FB',
                                        ' at ', pc);
                              If s[6] = nilproc Then
                                s[5] := s[5]+1
                              Else
                                Begin
                                  Release( 5 );
                                  AddReady( relpr );
                                  If WAKESEM Then
                                    Begin
(* awaken waiting process *)
                                      While ptab[lastready].nextp <> relpr Do
                                        lastready := ptab[lastready].nextp;
                                      If TRACE Then
                                        writeln( ' ':Indent*runpr, 'WAKEUP ',
                                                relpr);
                                      ps := wakeup
                                    End
                                  Else If TRACE Then
                                         writeln(' ':Indent*runpr, 'RELEASE ',
                                                 relpr)
                                End;
                              ps := kill;
(* add to free list *)
                              status := free;
                              nextp := freetop;
                              freetop := runpr
                            End;
                        6 :
                            Begin
(* semaphore wait *)
                              h1 := s[t];
                              t := t-1;
                              If s[h1] > 0 Then
                                Begin
                                  s[h1] := s[h1]-1;
                                  If TRACE Then
                                    writeln(' ':Indent*runpr, 'PASS ', h1,
                                            ' at ', pc)
                                End
                              Else
                                Begin
(* suspend running process *)
                                  RemoveReady;
                                  Suspend( h1 );
                                  If TRACE Then
                                    writeln( ' ':Indent*runpr, 'SUSPEND ', h1,
                                            ' at ', pc);
                                  ps := suspended
                                        106
                                End
                            End;
                        7 :
                            Begin
(* semaphore signal *)
                              h1 := s[t];
                              t := t-1;
                              If TRACE Then
                                writeln(' ':Indent*runpr, 'SIGNAL ', h1,
                                        ' at ', pc);
                              If s[h1+1] = nilproc Then
(* noone awaits this signal *)
                                s[h1] := s[h1]+1
                              Else
                                Begin
(* someone awaits this signal *)
                                  Release( h1 );
                                  AddReady( relpr );
                                  If TRACE Then
                                    writeln( ' ':Indent*runpr, 'Time waiting = ',
                                            ptab[relpr].tblocked, ' for ', h1 );
                                  ptab[relpr].tblocked := 0;
                                  If WAKESEM Then
                                    Begin
(* awaken waiting process *)
                                      While ptab[lastready].nextp <> relpr Do
                                        lastready := ptab[lastready].nextp;
                                      If TRACE Then
                                        writeln( ' ':Indent*runpr, 'WAKEUP ',
                                                relpr);
                                      ps := wakeup
                                    End
                                  Else If TRACE Then
                                         writeln(' ':Indent*runpr, 'RELEASE ',
                                                 relpr)
                                End
                            End;
                        8 : Case ir.y Of 
                              17 :
                                   Begin
                                     t := t+1;
                                     If t > stacklimit Then ps := stkchk
                                     Else s[t] := btoi(eof(Keys))
                                   End;
                              18 :
                                   Begin
                                     t := t+1;
                                     If t > stacklimit Then ps := stkchk
                                     Else s[t] := btoi(eoln(Keys))
                                   End;
                            End;
                        9 :
                            Begin
(* put parent process to sleep *)
                              If childcount > 0 Then
                                Begin
                                  tblocked := tstart + timer + totalwait;
                                  AddWait( runpr, tblocked );
                                  RemoveReady;
                                  If TRACE Then
                                    writeln( ' ':Indent*runpr, 'SLEEP ',
                                            runpr, ' at ', pc);
                                  status := sleeping;
                                  ps := sleep
                                End;
                            End;
                        107
                        10 : pc := ir.y;
(* jump *)
                        11 :
                             Begin
(* conditional jump *)
                               If s[t] = fals Then pc := ir.y;
                               t := t-1
                             End;
                        12 :
                             Begin
(* block all timeouts *)
                               lock := true
                             End;
                        13 :
                             Begin
(* allow timeouts again *)
                               lock := false
                             End;
                        14 :
                             Begin
(* for1up *)
                               h1 := s[t-1];
                               If h1 <= s[t] Then s[s[t-2]] := h1
                               Else
                                 Begin
                                   t := t-3;
                                   pc := ir.y
                                 End
                             End;
                        15 :
                             Begin
(* for2up *)
                               h2 := s[t-2];
                               h1 := s[h2]+1;
                               If h1 <= s[t] Then
                                 Begin
                                   s[h2] := h1;
                                   pc := ir.y
                                 End
                               Else t := t-3
                             End;
                        17 : ps := abort;
(* abort *)
                        18 :
                             Begin
(* mark stack *)
                               h1 := btab[tab[ir.y].ref].vsize;
                               If t+h1 > stacklimit Then ps := stkchk
                               Else
                                 Begin
                                   t := t+5;
                                   s[t-1] := h1-1;
                                   s[t] := ir.y
                                 End
                             End;
                        19 :
                             Begin
(* call *)
                               h1 := t-ir.y;
                               h2 := s[h1+4];
(* h2 points to tab *)
                               If TRACE Then
                                 writeln( ' ':Indent*runpr,
                                         'CALL ', tab[h2].name );
                               h3 := tab[h2].lev;
                               display[h3+1] := h1;
                               h4 := s[h1+3]+h1;
                               s[h1+1] := pc;
                               s[h1+2] := display[h3];
                               s[h1+3] := b;
                               For h3 := t+1 To h4 Do
                                 s[h3] := 0;
                               b := h1;
                               t := h4;
                               pc := tab[h2].adr
                             End;
                        21 :
                             Begin
(* index *)
                               h1 := ir.y;
(* h1 points to atab *)
                               h2 := atab[h1].low;
                               h3 := s[t];
                               If h3 < h2 Then ps := inxchk
                               Else If h3 > atab[h1].high Then ps := inxchk
                               Else
                                 Begin
                                   t := t-1;
                                   s[t] := s[t] + (h3-h2)*atab[h1].elsize
                                           108
                                 End
                             End;
                        22 :
                             Begin
(* load block *)
                               h1 := s[t];
                               t := t-1;
                               h2 := ir.y+t;
                               If h2 > stacklimit Then ps := stkchk
                               Else
                                 While t<h2 Do
                                   Begin
                                     t := t+1;
                                     s[t] := s[h1];
                                     h1 := h1+1
                                   End
                             End;
                        23 :
                             Begin
(* copy block *)
                               h1 := s[t-1];
                               h2 := s[t];
                               h3 := h1+ir.y;
                               While h1 < h3 Do
                                 Begin
                                   s[h1] := s[h2];
                                   h1 := h1+1;
                                   h2 := h2+1
                                 End;
                               t := t-2
                             End;
                        24 :
                             Begin
(* literal *)
                               t := t+1;
                               If t > stacklimit Then ps := stkchk
                               Else s[t] := ir.y
                             End;
                        27 :
                             Begin
(* read *)
                               If eof(Keys) Then ps := redchk
                               Else
                                 Case ir.y Of 
                                   1 : read(Keys,s[s[t]]);
                                   3 :
                                       Begin
                                         read(Keys,ch);
                                         s[s[t]] := ord(ch)
                                       End
                                 End;
                               t := t-1
                             End;
                        28 :
                             Begin
(* write string *)
                               h1 := s[t];
                               h2 := ir.y;
                               t := t-1;
                               chrcnt := chrcnt+h1;
                               If chrcnt > lineleng Then ps := lngchk;
                               Repeat
                                 write(stab[h2]);
                                 h1 := h1-1;
                                 h2 := h2+1
                               Until h1=0
                             End;
                        29 :
                             Begin
(* write1 *)
                               If ir.y=3 Then h1 := 1
                               Else h1 := 10;
                               chrcnt := chrcnt+h1;
                               If chrcnt > lineleng Then ps := lngchk
                               Else
                                 Case ir.y Of 
                                   1 : write(s[t]:6);
                                   2 : write(itob(s[t]));
                                   3 : If (s[t] < charl) Or (s[t] > charh) Then
                                         ps := inxchk
                                       Else write(chr(s[t]))
                                 End;
                               109
                               t := t-1
                             End;
                        31 : ps := fin;
(* halt *)
                        32 :
                             Begin
(* exit procedure *)
                               t := b-1;
                               pc := s[b+1];
                               b := s[b+3]
                             End;
                        33 :
                             Begin
(* exit function *)
                               t := b;
                               pc := s[b+1];
                               b := s[b+3]
                             End;
                        34 : s[t] := s[s[t]];
                        35 : s[t] := btoi(Not itob(s[t]));
                        36 : s[t] := -s[t];
                        37 :
                             Begin
(* duplicate *)
                               t := t+1;
                               If t>stacklimit Then ps := stkchk
                               Else s[t] := s[t-1]
                             End;
                        38 :
                             Begin
(* store *)
                               s[s[t-1]] := s[t];
                               t := t-2
                             End;
                        40 :
                             Begin
(* comm *)
                               selcount := 0;
                               setptr := Nil;
                               If s[t] = sentinel Then
                                 ps := guardchk
                               Else If ((s[t] = send) And (chantab[s[t-3]].owner = runpr)) Or
                                       ((s[t]=receive) And (chantab[s[t-4]].owner<>runpr)) Then
                                      ps := chanchk
                               Else
                                 Begin
                                   last := Nil;
                                   While s[t] <> sentinel Do
                                     Begin
                                       If s[t] = receive Then (* swap addr & chan *)
                                         Begin
                                           h1 := s[t-3];
                                           s[t-3] := s[t-4];
                                           s[t-4] := h1
                                         End;
                                       selcount := selcount + 1;
                                       EnQueue( t, selcount, last, (s[t-5]=sentinel) );
                                       t := t-5
                                     End;
                                   h1 := random( selcount );
                                   For h4 := 1 To h1 Do
                                     setptr := setptr^.setlink;
(* pick a comm stmt *)
                                   tmpptr := setptr;
                                   serviced := false;
                                   Repeat
                                     h2 := tmpptr^.channel;
                                     If h2 = 0 Then
                                       110
                                       Begin
                                         pc := tmpptr^.resume;
                                         serviced := true;
                                         CancelNodes( tmpptr )
                                       End
                                     Else If (chantab[h2].sendcount <> 0) And
                                             (chantab[h2].receiveq <> Nil) Then
                                            Begin
                                              Rendezvous( tmpptr );
                                              serviced := true
                                            End
                                     Else
                                       tmpptr := tmpptr^.setlink
                                   Until serviced Or (tmpptr = setptr);
                                   If Not serviced Then
                                     If ir.y = select Then (* comm is part of guard *)
                                       WaitforRen( select, 0 )
                                   Else (* normal comm *)
                                     WaitforRen( s[t+5], tab[s[t+2]].adr );
                                   t := t-1 (* pop sentinel *)
                                 End
                             End;
                        41 :
                             Begin
(* post *)
                               s[t+1] := runpr;
                               s[t+2] := pc + 1;
                               s[t+3] := ir.y;
(* send/receive *)
                               t := t+3
                             End;
                        42 :
                             Begin
(* getchannel *)
                               chantab[s[t]].owner := runpr;
                               chantab[s[t]].uniqueowner := ptab[runpr].procno;
                               t := t-1
                             End;
                        43 :
                             Begin
(* post pure Boolean *)
                               s[t+1] := 0;
(* comm *)
                               s[t+2] := 0;
(* channel *)
                               s[t+3] := runpr;
(* process *)
                               s[t+4] := pc + 1;
(* resume *)
                               s[t+5] := purebool;
(* direction *)
                               t := t+5
                             End;
                        45 :
                             Begin
                               t := t-1;
                               s[t] := btoi(s[t]=s[t+1])
                             End;
                        46 :
                             Begin
                               t := t-1;
                               s[t] := btoi(s[t]<>s[t+1])
                             End;
                        47 :
                             Begin
                               t := t-1;
                               s[t] := btoi(s[t]<s[t+1])
                             End;
                        48 :
                             Begin
                               t := t-1;
                               s[t] := btoi(s[t]<=s[t+1])
                             End;
                        49 :
                             Begin
                               t := t-1;
                               s[t] := btoi(s[t]>s[t+1])
                             End;
                        50 :
                             Begin
                               t := t-1;
                               s[t] := btoi(s[t]>=s[t+1])
                             End;
                        51 :
                             Begin
                               t := t-1;
                               s[t] := btoi(itob(s[t]) Or itob(s[t+1]))
                             End;
                        52 :
                             Begin
                               t := t-1;
                               s[t] := s[t]+s[t+1]
                             End;
                        53 :
                             Begin
                               t := t-1;
                               s[t] := s[t]-s[t+1]
                             End;
                        56 :
                             Begin
                               t := t-1;
                               s[t] := btoi(itob(s[t]) And itob(s[t+1]))
                             End;
                        111
                        57 :
                             Begin
                               t := t-1;
                               s[t] := s[t]*s[t+1]
                             End;
                        58 :
                             Begin
                               t := t-1;
                               If s[t+1] = 0 Then ps := divchk
                               Else s[t] := s[t] Div s[t+1]
                             End;
                        59 :
                             Begin
                               t := t-1;
                               If s[t+1] = 0 Then ps := divchk
                               Else s[t] := s[t] Mod s[t+1]
                             End;
                        62 : If eof(Keys) Then ps := redchk
                             Else readln(Keys);
                        63 :
                             Begin
                               writeln;
                               lncnt := lncnt+1;
                               chrcnt := 0;
                               If lncnt > linelimit Then ps := linchk
                             End;
                      End;
(* case *)
                    End;
(* with *)
                  lastpr := runpr;
                  If stepcount > 0 Then stepcount := stepcount-1;
                  If lastready = nilproc Then
                    ps := deadlock
                  Else
                    Begin
                      If (ps = run) And (stepcount = 0) And Not lock Then
                        Begin
                          If TRACE Then
                            writeln( ' ':Indent*runpr, 'TIMEOUT at ',
                                    ptab[runpr].pc);
                          ps := timeout;
                          If code[ptab[runpr].pc].f = 5 Then
                            Begin
                              inserted := false;
                              With ptab[runpr] Do
                                clock := tstart + timer + totalwait;
(* temporarily remove Runpr from Ready Q *)
                              ptab[lastready].nextp := ptab[runpr].nextp;
                              before := lastready;
                              after := ptab[lastready].nextp;
                              While Not inserted Do
                                Begin
                                  With ptab[after] Do
                                    afterclock := tstart + timer + totalwait;
                                  If afterclock = clock Then
                                    Begin
                                      ptab[runpr].nextp := after;
                                      ptab[before].nextp := runpr;
                                      inserted := true
                                    End
                                  Else
                                    Begin
                                      before := ptab[before].nextp;
                                      after := ptab[after].nextp;
                                      If before = lastready Then
                                        Begin
                                          ptab[runpr].nextp := after;
                                          ptab[before].nextp := runpr;
                                          inserted := true;
                                          nextproc
                                        End
                                        112
                                    End
                                End
                            End
                          Else
                            nextproc
                        End;
                      If ps In [timeout,kill,suspended,sleep,wakeup] Then
                        Begin
                          If ps = timeout Then
                            ptab[runpr].status := ready;
                          runpr := ptab[lastready].nextp;
                          ptab[runpr].status := running;
                          If TRACE Then
                            Begin
                              writeln;
                              writeln( ' ':Indent*runpr, 'RESTART ',
                                      runpr, ' at ', ptab[runpr].pc)
                            End;
                          If USEQUANTUM Then setquantum
                        End
                    End
                Until Not (ps In [run,timeout,sleep,suspended,kill,wakeup]);
(* ps in [fin, xxxchk, or deadlock] *)
                writeln;
                If ps = fin Then
                  ReportProcess( main )
                Else
                  PostMortemDump;
                RuntimeSummary;
(* Print times for all processes *)
                RelUtilization;
(* Print relative utilization percentages *)
                AbsUtilization;
(* Print absolute utilization percentages & graphs *)
                If ShowInternal Then
                  Begin
                    DumpSumtab;
(* Print contents of Sumtab *)
                    DumpWaitlist (* Print wait & signal times for each process *)
                  End;
                DisplayGraph;
(* Print graphical display of runtime use of processors *)
              End;
(* interpret *)