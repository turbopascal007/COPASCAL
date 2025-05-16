program pascals(input, output);
(*author: N. Wirth,  E.T.H.i ch--8092 Zurich, 1. 3. 76*)
(*modified: M. Ben-Ari, Tel Aviv Univ., 1980          *)
(*recreated by B. Nielsen, Aarhus University, 2000    *)
label 99;
const
  nkw  =        26;     (* no. of key words                         *)
  alng =        10;     (* no. of significant chars in identifiers  *)
  llng =       121;     (* input line length                        *)
  kmax =        15;     (* max no. of significant digits            *) 
  tmax =        70;     (* size of table                            *)
  bmax =        20;     (* size of block-table                      *)
  amax =        10;     (* size of array-table                      *)
  cmax =       500;     (* size of code                             *)
  lmax =         7;     (* maximum level                            *)
  smax =       150;     (* size of string-table                     *)
  omax =        63;     (* highest order code                       *)
  xmax =    131071;     (* 2**17 - 1                                *)
  nmax = 281474976710655;      (* 2**48-1                           *)
  lineleng =   132;     (* output line length                       *) 
  linelimit =  400;     (* max lines to print                       *)
  stmax =     1400;     (* stacksize                                *)
  stkincr =    200;     (* stacksize for each process               *)
  pmax =         3;     (* max concurrent processes                 *)

type 
  symbol = (intcon,charcon,string,
            notsy,plus,minus,times,idiv,imod,andsy,orsy,
            eql,neq,gtr,geq,lss,leq,
            lparent,rparent,lbrack,rbrack,comma,semicolon,period,
            colon,becomes,constsy,typesy,varsy,functionsy,
            proceduresy,arraysy,programsy,ident,
            beginsy,ifsy,repeatsy,whilesy,forsy,
            endsy,elsesy,untilsy,ofsy,dosy,tosy,thensy);

  index  = -xmax .. +xmax;
  alfa   = packed array [1..alng] of char;
  object = (konstant,variable,type1,prozedure,funktion);
  types  = (notyp,ints,bools,chars,arrays);
  er=(erid,ertyp,erkey,erpun,erpar,ernf,erdup,erch,ersh,erln);
  symset = set of symbol;
  typset = set of types;
  item   = record
             typ: types; 
             ref: index;
           end;
  order  = packed record
             f: -omax..+omax;
             x: -lmax..+lmax;
             y: -nmax..+nmax;
           end;

var
  sy: symbol;          (*last symbol read by insymbol*)
  id: alfa;            (*identifier from insymbol*)
  inum: integer;       (*integer from insymbol*)   
  sleng: integer;      (*string length*)
  ch: char;            (*last character read from source program*)
  line: array [1..llng] of char;
  cc: integer;         (*character count*)
  lc: integer;         (*program location counter*)
  ll: integer;         (*length of current line*)
  errs: set of er;
  errpos: integer;
  progname: alfa;
  skipflag: boolean;
  constbegsys,typebegsys,blockbegsys,facbegsys,statbegsys: symset;
  key: array [1..nkw] of alfa;
  ksy: array [1..nkw] of symbol;
  sps: array [char] of symbol;  (*special symbols*)
  t,a,b,sx,c1,c2: integer;  (*indices to tables*)
  stantyps: typset;
  display: array [0 .. lmax] of integer;

  tab:     array  [0..tmax] of      (*identifier table*)
             packed record
               name: alfa;  link: index;
               obj: object; typ: types;
               ref: index;  normal: boolean;
               lev: 0..lmax; adr: integer;
             end;
  atab:    array  [1..amax] of      (*array-table*)
             packed record
               inxtyp, eltyp: types;
               elref, low, high, elsize, size: index;
             end;
  btab:    array  [1..bmax] of      (*block-table*)
             packed record
               last, lastpar, psize, vsize: index;
             end;
  stab:    packed array [0..smax] of char;  (*string table*)
  code:    array [0 .. cmax] of order;
  
  procedure errormsg;
  var
    k:   er;
    msg: array [er] of alfa;
  begin
    msg[erid]  := 'identifier';
    msg[ertyp] := 'type      ';
    msg[erkey] := 'keyword   ';
    msg[erpun] := 'punctuatio';
    msg[erpar] := 'parameter ';
    msg[ernf]  := 'not found ';
    msg[erdup] := 'duplicate ';
    msg[erch]  := 'character ';
    msg[ersh]  := 'too short ';
    msg[erln]  := 'too long  ';
    message('compilation errors');
    writeln; writeln(' key words');
    for k:= erid to erln do 
      if k in errs then
        writeln(ord(k),' ',msg[k])
  end (* errormsg*);

  procedure endskip;
  begin (*underline skipped part of input*)
    while errpos < cc do
    begin 
      write('_');
      errpos := errpos + 1;
    end;
    skipflag:= false;
  end (*endskip*);

  procedure nextch;   (*read next character; process line end*)
  begin
    if cc = ll then
    begin
      if eof(input) then
      begin
        writeln;
        writeln(' program incomplete');
        errormsg;
        goto 99;
      end;
      if errpos <> 0 then
      begin 
        if skipflag then
          endskip;
        writeln;
        errpos := 0
      end;
      write(lc:5, '  ');
      ll := 0; 
      cc := 0;
      while not eoln(input) do
      begin
        ll := ll+1; 
        read(ch); 
        write(ch); 
        line[ll] := ch
      end;
      writeLn;
      ll:=ll+1; 
      read(line[ll])
    end;
    cc := cc+1;
    ch := line[cc];
  end (*nextch*);

  procedure error(n: er);
  begin
    if errpos=0 then
      write(' ****');
    if cc>errpos then
    begin
      write(' ',cc-errpos,'''', ord(n):2);
      errpos:= cc+3;
      errs:=errs+[n];
    end
  end (*error*);

  procedure fatal(n: integer);
  var
    msg: array [1..6] of alfa;
  begin
    writeln;
    errormsg;
    msg[1] := 'identifier';
    msg[2] := 'procedures';
    msg[3] := 'strings   ';
    msg[4] := 'arrays    ';
    msg[5] := 'levels    ';
    msg[6] := 'code      ';
    writeln(' compiler table for ', msg[n], ' is too small');
    goto 99 (* terminate compilation*)
  end (*fatal*);

  procedure insymbol;           (*reads next symbol*)
  label
    1,2,3;
  var
    i,j,k,e: integer;
  
  begin (*insymbol*) 
  1:while ch = ' ' do
      nextch;
    case ch of
      'a','b','c','d','e','f','g','h','i',
      'j','k','l','m','n','o','p','q','r',
      's','t','u','v','w','x','y','z':
      begin (*identifier or wordsymbol*)  
        k := 0;
        id := '          ';
        repeat
          if k < alng then
          begin
            k := k+1;
            id[k] := ch
          end;
          nextch
        until not (ch in ['a'..'z','0'..'9']);
        i := 1;         (*binary search*)
        j := nkw;
        repeat
          k := (i+j) div 2;
          if id <= key[k] then
            j := k-1;
          if id >= key[k] then 
            i := k+1;
        until i > j;
        if i-1 > j then
          sy := ksy[k]
        else
          sy := ident
      end
      '0','1','2','3','4','5','6','7','8','9':
      begin (*number*)
        k := 0;
        inum := 0;
        sy := intcon;
        repeat
          inum := inum*10 + ord(ch) - ord('0');
          k := k+1;
          nextch
        until not (ch in ['0'..'9']);
        if (k > kmax) or (inum > nmax) then
        begin
          error(erln);
          inum := 0;
          k := 0
        end;     
      end;     
      ':',col: 
      begin
        nextch;
        if ch = '=' then
        begin
          sy := becomes;
          nextch
        end
        else
          sy := colon
      end;
      '<' :
      begin
        nextch;
        if ch = '=' then
        begin
          sy := leq;
          nextch
        end
        else
          if ch = '>' then
          begin
            sy := neq;
            nextch
          end
          else
            sy := lss
      end;
      '>' :
      begin
        nextch;
        if ch = '=' then
          begin
            sy := geq;
            nextch 
          end
          else
            sy := gtr
      end;
      '.' :
      begin
        nextch;
        if ch = '.' then
        begin
          sy := colon;
          nextch
        end
        else
          sy := period
      end;
      '''': 
      begin
        k := 0;
      2:nextch;
        if ch = '''' then
        begin
          nextch;
          if ch <> '''' then
            goto 3
        end;
        if sx+k = smax then
          fatal(7);
        stab[sx+k] := ch;
        k := k+1;
        if cc = 1 then (*end of line*) 
          k := 0
        else
          goto 2;
      3:if k = 1 then
        begin
          sy := charcon; 
          inum := ord(stab[sx])
        end
        else
          if k = 0 then
          begin
            error(ersh);
            sy := charcon;
            inum := 0
          end
          else
          begin
            sy := stringsy;
            inum := sx;
            sleng := k;
            sx := sx+k
          end
      end;
      '(' :
      begin
        nextch;
        if ch <> '*' then
          sy := lparent
        else
        begin (*comment*)
          nextch;
          repeat
            while ch <> '*' do
              nextch;
            nextch
          until ch = ')';
          nextch;
          goto 1
        end
      end;
      '+', '-', '*', ')', '=', ',', '[', ']', ';' :
      begin
        sy := sps[ch];
        nextch
      end;
      '$', '!', '@', '\', ':', '_', '?', '`', '"', '&', '|':
      begin 
        error(erch);
        nextch;
        goto 1
      end;
    end;
  end (*insymbol*);

  procedure enter(x0: alfa; x1: object;
                  x2: types; x3: integer);
  begin
    t := t+1;   (*enter standard identifier*)
    with tab[t] do
    begin
      name := x0;
      link := t-1;
      obj := x1;
      typ := x2;
      ref := 0;
      normal := true;
      lev := 0;
      adr := x3
    end
  end (*enter*);

  procedure enterarray(tp: types; l,h: integer);
  begin
    if l  > h then
      error(ertyp);
    if (abs(l)>xmax) or (abs(h)>xmax) then
    begin
      error(ertyp);
      l := 0;
      h := 0;
    end;
    if a = amax then
      fatal(4)
    else
    begin
      a := a+1;
      with atab[a] do
      begin
        inxtyp := tp;
        low := l;
        high := h
      end
    end
  end (*enterarray*);

  procedure enterblock;
  begin
    if b = bmax then
      fatal(2)
    else
    begin
      b := b+1;
      btab[b].last := 0;
      btab[b].lastpar := 0
    end
  end (*enterblock*);

  procedure emit(fct: integer);
  begin
    if lc = cmax then
      fatal(6);
    code[lc].f := fct;
    lc := lc+1
  end (*emit*);

  procedure emit1(fct,b: integer);
  begin 
    if lc = cmax then
      fatal(6);
    with code[lc] do
    begin
      f := fct;
      y := b
    end;
    lc := lc+1
  end (*emit1*);

  procedure emit2(fct,a,b: integer);
  begin
    if lc = cmax then
      fatal(6);
    with code[lc] do
    begin
      f := fct;
      x := a;
      y := b
    end;
    lc := lc+1
  end (*emit2*);

  procedure block(fsys: symset; isfun: boolean; level: integer);
  type
    conrec = record
               tp: types;
               i: integer;
             end;
     
  var
    dx: integer;    (*data allocation index*)
    prt: integer;   (*t-index of this procedure*)
    prb: integer;   (*b-index of this procedure*)
    x: integer;
   
    procedure skip(fsys: symset; n:er);
    begin
      error(n);
      while not (sy in fsys) do
        insymbol;
      if skipflag then
        endskip;
    end (*skip*);
        
    procedure test(s1,s2: symset; n: er);
    begin
      if not (sy in s1) then 
        skip(s1+s2,n) 
    end (*test*);
     
    procedure testsemicolon;
    begin
      if sy = semicolon then
        insymbol
      else
        error(erpun);
      test([ident]+blockbegsys, fsys, erkey)
    end (*testsemicolon*);
     
    procedure enter(id: alfa; k: object);
    var
      j,l: integer;
    begin
      if t = tmax then
        fatal(1)
      else
      begin
        tab[0].name := id;
        j := btab[display[level]].last;
        l := j;
        while tab[j].name <> id do
          j := tab[j].link;
        if j <> 0 then
          error(erdup)
        else
        begin
          t := t+1;
          with tab[t] do
          begin
            name := id;
            link := l;
            obj := k;
            typ := notyp;
            ref := 0;
            lev := level;
            adr := 0
          end;
          btab[display[level]].last := t
        end
      end
    end (*enter*);
     
    function loc(id: alfa): integer;
    var
      i,j: integer;     (*locate id in table*)
    begin
      i := level;
      tab[0].name := id;   (*sentinel*)
      repeat
        j := btab[display[i]].last;
        while tab[j].name <> id do
          j := tab[j].link;
        i := i-1;
      until (i<0) or (j<>0);
      if j = 0 then
        error(ernf);
      loc := j
    end (*loc*);
     
    procedure entervariable;
    begin
      if sy = ident then
      begin
        enter(id,variable);
        insymbol
      end
      else
        error(erid)
    end (*entervariable*);
     
    procedure constant(fsys: symset; var c: conrec);
    var
      x, sign: integer;
    begin 
      c.tp := notyp; 
      c.i := 0;
      test(constbegsys, fsys, erkey);
      if sy in constbegsys then
      begin
        if sy = charcon then
        begin 
          c.tp := chars; 
          c.i := inum; 
          insymbol
        end
        else
        begin
          sign := 1;
          if sy in [plus,minus] then
          begin
            if sy = minus then
              sign := -1;
            insymbol
          end;
          if sy = ident then
          begin
            x := loc(id);
            if x <> 0 then
              if tab[x].obj <> konstant then 
                error(ertyp) 
              else
              begin
                c.tp := tab[x].typ;
                c.i := sign*tab[x].adr
              end;
            insymbol
          end 
          else
            if sy = intcon then
            begin
              c.tp := ints;
              c.i := sign*inum; 
              insymbol
            end
            else
              skip(fsys,erkey)                   
        end;
        test(fsys, [], erkey)
      end
    end (*constant*);
        
    procedure typ(fsys: symset; var tp: types; var rf, sz: integer);
    var
      x: integer;
      eltp: types; elrf: integer;
      elsz, offset, t0,t1: integer;
         
      procedure arraytyp(var aref,arsz: integer);
      var
        eltp: types;
        low, high: conrec;
        elrf, elsz: integer;
      begin
        constant([colon,rbrack,rparent,ofsy]+fsys, low);
        if sy = colon then
          insymbol
        else
          error(erpun);
        constant([rbrack,comma,rparent,ofsy]+fsys, high);
        if high.tp <> low.tp then
        begin
          error(ertyp);
          high.i := low.i
        end;
        enterarray(low.tp, low.i, high.i); 
        aref := a;
        if sy = comma then
        begin
          insymbol; 
          eltp := arrays; 
          arraytyp(elrf,elsz)
        end
        else
        begin
          if sy = rbrack then 
            insymbol 
          else
            error(erpun);
          if sy = ofsy then
            insymbol 
          else 
            error(erkey);
          typ(fsys,eltp,elrf,elsz)
        end;
        with atab[aref] do
        begin
          arsz := (high-low+1)*elsz; 
          size:=arsz;
          eltyp := eltp;
          elref := elrf;
          elsize := elsz
        end;
      end (*arraytyp*);
         
    begin (*typ*)
      tp := notyp;
      rf := 0;
      sz := 0;
      test(typebegsys, fsys, erid);
      if sy in typebegsys then
      begin
        if sy = ident then
        begin
          x := loc(id);
          if x <> 0 then
            with tab[x] do
              if obj <> type1 then
                error(ertyp)
              else
              begin
                tp := typ; 
                rf := ref; 
                sz := adr;
                if tp = notyp then
                  error(ertyp)
              end;
          insymbol
        end
        else
          if sy = arraysy then
          begin
            insymbol;
            if sy = lbrack then
              insymbol
            else
              error(erpun);
            tp := arrays;
            arraytyp(rf,sz)
          end
          else
            test(fsys, [], erkey)
        end               
    end (*typ*);

    procedure parameterlist;      (*formal parameter list*)
    var
      tp: types;
      rf, sz, x, t0: integer;
      valpar: boolean;
    begin
      insymbol;
      tp := notyp;
      rf := 0;
      sz := 0;
      test([ident,varsy], fsys+[rparent], erpar);
      while sy in [ident,varsy] do
      begin
        if sy <> varsy then
          valpar := true
        else
        begin
          insymbol;
          valpar := false
        end;
        t0 := t;
        entervariable;
        while sy = comma do
        begin
          insymbol;
          entervariable;
        end;
        if sy = colon then 
        begin
          insymbol;
          if sy <> ident then
            error(erid)
          else
          begin
            x := loc(id);
            insymbol;
            if x <> 0 then
              with tab[x] do
                if obj <> type1 then
                  error(ertyp)
                else
                begin
                  tp := typ;
                  rf := ref;
                  if valpar then 
                    sz := adr
                  else
                    sz := 1
                end
          end;
          test([semicolon,rparent], [comma,ident]+fsys, erpun)
        end
        else
          error(erpun);
        while t0 < t do
        begin
          t0 := t0+1;
          with tab[t0] do
          begin
            typ := tp;
            ref := rf;
            normal := valpar;
            adr := dx;
            lev := level;
            dx := dx + sz
          end
        end;
        if sy <> rparent then
        begin
          if sy = semicolon then
            insymbol
          else
            error(erpun);
          test([ident,varsy], [rparent]+fsys, erkey)
        end
      end (*while*);
      if sy = rparent then
      begin
        insymbol;
        test([semicolon,colon], fsys, erkey)
      end
      else
        error(erpun)
    end (*parameterlist*);
        
    procedure constantdeclaration;
    var
      c: conrec;
    begin
      insymbol;
      test([ident], blockbegsys, erid);
      while sy = ident do
      begin
        enter(id,konstant);
        insymbol;
        if sy = eql then
          insymbol
        else
          error(erpun);
        constant([semicolon,comma,ident]+fsys,c);
        tab[t].typ := c.tp;
        tab[t].ref := 0;
        tab[t].adr := c.i;
        testsemicolon
      end  
    end (*constantdeclaration*);
        
    procedure typedeclaration;
    var
      tp: types; rf, sz, t1: integer;
    begin
      insymbol;
      test([ident], blockbegsys, erid);
      while sy = ident do
      begin
        enter(id,type1);
        t1 := t;
        insymbol;
        if sy = eql then
          insymbol
        else
          error(erpun);
        typ([semicolon,comma,ident]+fsys, tp, rf, sz);
        with tab[t1] do
        begin
          typ := tp;
          ref := rf;
          adr := sz
        end;
        testsemicolon
      end
    end (*typedeclaration*);
        
    procedure variabledeclaration;
    var
      t0, t1, rf, sz: integer;
      tp: types;
    begin
      insymbol;
      while sy = ident do
      begin
        t0 := t;
        entervariable;
        while sy = comma do
        begin
          insymbol;
          entervariable;
        end;
        if sy = colon then
          insymbol
        else
          error(erpun);
        t1 := t;
        typ([semicolon,comma,ident]+fsys, tp, rf, sz);
        while t0 < t1 do
        begin 
          t0 := t0+1;
          with tab[t0] do
          begin
            typ := tp;
            ref := rf;
            lev := level;
            adr := dx;
            normal := true;
            dx := dx + sz
          end
        end;
        testsemicolon
      end
    end (*variabledeclaration*);
        
    procedure procdeclaration;
    var
      isfun: boolean;
    begin
      isfun := sy = functionsy;
      insymbol;
      if sy <> ident then
      begin
        error(erid);
        id := '          ';
      end;
      if isfun then
        enter(id,funktion)
      else
        enter(id,prozedure);
      tab[t].normal := true;
      insymbol;
      block([semicolon]+fsys, isfun, level+1);
      if sy = semicolon then
        insymbol
      else
        error(erpun);
      emit(32+ord(isfun))    (*exit*)
    end (*procdeclaration*);
     
    procedure statement(fsys: symset);
    var
      i: integer;
      x: item;

      procedure expression(fsys: symset; var x: item); forward;
            
      procedure selector(fsys: symset; var v: item);
      var
        x: item;
        a,j: integer;
      begin (*sy in [lparent, lbrack, period]*)
        if sy <> lbrack then
          error(ertyp);
        repeat
          insymbol;
          expression(fsys+[comma,rbrack], x);
          if v.typ <> arrays then
            error(ertyp) 
          else
          begin
            a := v.ref;
            if atab[a].inxtyp <> x.typ then
              error(ertyp) 
            else
              emit1(21,a);
            v.typ := atab[a].eltyp; 
            v.ref := atab[a].elref;
          end
        until sy <> comma;
        if sy = rbrack then
          insymbol
        else
          error(erpun);
        test(fsys,[],erkey);
      end (*selector*);
            
      procedure call(fsys: symset; i: integer);
      var
        x: item;
        lastp, cp, k: integer;
      begin
        emit1(18,i);  (*mark stack*)
        lastp := btab[tab[i].ref].lastpar;
        cp := i;
        if sy = lparent then
        begin (*actual parameter list*)
          repeat
            insymbol;
            if cp >= lastp then
              error(erpar)
            else
            begin
              cp := cp+1;
              if tab[cp].normal then
              begin (*value parameter*)
                expression(fsys+[comma,colon,rparent], x);
                if x.typ=tab[cp].typ then
                begin
                  if x.ref <> tab[cp].ref then
                    error(ertyp)
                  else
                    if x.typ = arrays then
                      emit1(22,atab[x.ref].size)
                end
                else
                  if x.typ<>notyp then
                    error(ertyp);
              end
              else
              begin (*variable parameter*)
                if sy <> ident then
                  error(erid)
                else
                begin
                  k := loc(id);
                  insymbol;
                  if k <> 0 then
                  begin
                    if tab[k].obj <> variable then
                      error(erpar);
                    x.typ := tab[k].typ;
                    x.ref := tab[k].ref;
                    if tab[k].normal then
                      emit2(0,tab[k].lev,tab[k].adr)
                    else
                      emit2(1,tab[k].lev,tab[k].adr);
                    if sy = lbrack then
                      selector(fsys+[comma,colon,rparent], x);
                    if (x.typ<>tab[cp].typ) or (x.ref<>tab[cp].ref) then
                      error(ertyp)
                  end
                end
              end
            end;
            test([comma,rparent], fsys, erkey)
          until sy <> comma;
          if sy = rparent then
            insymbol
          else
            error(erpun)
        end;
        if cp < lastp then
          error(erpar); (*too few actual parameters*)
        emit1(19, btab[tab[i].ref].psize-1);
        if tab[i].lev < level then
          emit2(3, tab[i].lev, level)
      end (*call*);
            
      function resulttype(a,b: types): types;
      begin
        if (a>ints) or (b>ints) then
        begin
          error(ertyp); 
          resulttype := notyp
        end
        else
          if (a=notyp) or (b=notyp) then
            resulttype := notyp 
          else
            resulttype := ints
      end (*resulttype*);
 
      procedure expression;
      var
        y:item;
        op:symbol;
                            
        procedure simpleexpression(fsys: symset; var x: item);
        var
          y:item;
          op:symbol;
                 
          procedure term(fsys:symset; var x:item);
          var 
            y:item; 
            op:symbol; 
            ts:typset;
                   
            procedure factor(fsys:symset; var x: item);
            var
              i,f: integer;
                     
            begin (*factor*)
              x.typ := notyp;
              x.ref := 0;
              test(facbegsys, fsys, erpun);
              while sy in facbegsys do
              begin
                if sy = ident then
                begin
                  i := loc(id);
                  insymbol;
                  with tab[i] do
                    case obj of
                    konstant:
                    begin
                      x.typ := typ;
                      x.ref := 0;
                      emit1(24,adr)
                    end;
                    variable:
                    begin
                      x.typ := typ;
                      x.ref := ref;
                      if sy = lbrack then
                      begin
                        if normal then
                          f := 0
                        else
                          f := 1;
                        emit2(f, lev, adr);
                        selector(fsys,x);
                        if x.typ in stantyps then 
                          emit(34)
                      end
                      else
                      begin
                        if x.typ in stantyps then
                          if normal then
                            f:=1
                          else 
                            f:=2
                        else
                          if normal then
                            f:=0
                          else
                            f:=1;
                        emit2(f,lev,adr)
                      end
                    end;
                    type1, prozedure:
                      error(ertyp);
                    funktion: 
                    begin
                      x.typ := typ;
                      if lev <> 0 then
                        call(fsys, i)
                      else
                        emit1(8,adr);
                      end
                    end (*case,with*)
                  end
                  else
                    if sy in [charcon,intcon] then
                    begin
                      if sy = charcon then
                        x.typ := chars
                      else
                        x.typ := ints;
                      emit1(24, inum);
                      x.ref := 0; 
                      insymbol
                    end 
                    else
                      if sy = lparent then
                      begin
                        insymbol;
                        expression(fsys+[rparent], x);
                        if sy = rparent then
                          insymbol
                        else
                          error(erpun)
                      end 
                      else
                       if sy = notsy then
                       begin insymbol; factor(fsys,x);
                         if x.typ=bools then
                           emit(35)
                         else
                           if x.typ<>notyp then
                             error(ertyp)
                       end;
                test(fsys, facbegsys, erkey)
              end (*while*)
            end (*factor*);
                   
          begin (*term*)
            factor(fsys+[times,idiv,imod,andsy], x);
            while sy in [times,idiv,imod,andsy] do
            begin
              op := sy;
              insymbol;
              factor(fsys+[times,idiv,imod,andsy], y);
              if op = times then
              begin
                x.typ := resulttype(x.typ, y.typ);
                if x.typ = ints then
                  emit(57);
              end
              else
                if op = andsy then
                begin
                  if (x.typ=bools) and (y.typ=bools) then
                    emit(56)
                  else
                  begin
                    if (x.typ<>notyp) and (y.typ<>notyp) then
                      error(ertyp);
                    x.typ := notyp
                  end
                end
                else
                begin (*op in [idiv,imod]*)
                  if (x.typ=ints) and (y.typ=ints) then
                    if op=idiv then
                      emit(58)
                    else
                      emit(59)
                  else
                  begin
                    if (x.typ<>notyp) and (y.typ<>notyp) then
                      error(ertyp);
                    x.typ := notyp
                  end
                end
            end
          end (*term*);
                
        begin (*simpleexpression*)
          if sy in [plus,minus] then
          begin 
            op := sy;
            insymbol;
            term(fsys+[plus,minus], x);
            if x.typ > ints then
              error(ertyp)
            else
              if op = minus then
                emit(36)
          end
          else
            term(fsys+[plus,minus,orsy], x);
          while sy in [plus,minus,orsy] do
          begin
            op := sy;
            insymbol;
            term(fsys+[plus,minus,orsy], y);
            if op = orsy then 
            begin
              if (x.typ=bools) and (y.typ=bools) then
                emit(51)
              else
              begin
                if (x.typ<>notyp) and (y.typ<>notyp) then
                  error(ertyp);
                x.typ := notyp
              end
            end
            else
            begin
              x.typ := resulttype(x.typ, y.typ);
              if x.typ = ints then
                if op = plus then
                  emit(52)
                else
                  emit(53);
            end
          end
        end (*simpleexpression*);
               
      begin (*expression*)
        simpleexpression(fsys+[eql,neq,lss,leq,gtr,geq], x);
        if sy in [eql,neq,lss,leq,gtr,geq] then
        begin
          op := sy;
          insymbol;
          simpleexpression(fsys, y);
          if (x.typ in [notyp,ints,bools,chars]) and (x.typ = y.typ) then
            case op of
              eql: emit(45);
              neq: emit(46);
              lss: emit(47);
              leq: emit(48);
              gtr: emit(49);
              geq: emit(50);
            end
          else
            error(ertyp);
          x.typ := bools
        end
      end (*expression*);
            
      procedure assignment(lv,ad: integer);
      var 
        x,y: item;
        f: integer;
      (*tab[i].obj in [variable,prozedure]*)
      begin
        x.typ := tab[i].typ;
        x.ref := tab[i].ref;
        if tab[i].normal then
          f := 0 
        else
          f := 1;
        emit2(f, lv, ad);
        if sy = lbrack then
          selector([becomes,eql]+fsys, x);
        if sy = becomes then
          insymbol
        else
          error(erpun);
        expression(fsys, y);
        if x.typ = y.typ then
          if x.typ in stantyps then
            emit(38)
          else
            if x.ref <> y.ref then
              error(ertyp)
            else
              if x.typ = arrays then
                emit1(23, atab[x.ref].size)
              else 
                error(ertyp);
      end (*assignment*);
            
      procedure compoundstatement;
      begin
        insymbol;
        statement([semicolon,endsy]+fsys);
        while sy in [semicolon]+statbegsys do
        begin
          if sy = semicolon then
            insymbol
          else
            error(erpun);
          statement([semicolon,endsy]+fsys)
        end;
        if sy = endsy then
          insymbol
        else
          error(erkey)
      end (*compoundstatement*);
            
      procedure ifstatement;
      var
        x: item;
        lc1,lc2: integer;
      begin
        insymbol;
        expression(fsys+[thensy,dosy], x);
        if not (x.typ in [bools,notyp]) then
          error(ertyp);
        lc1 := lc;
        emit(11);  (*jmpc*)
        if sy = thensy then
          insymbol
        else
          error(erkey);
        statement(fsys+[elsesy]);
        if sy = elsesy then
        begin
          insymbol;
          lc2 := lc;
          emit(10);
          code[lc1].y := lc;
          statement(fsys);
          code[lc2].y := lc
        end
        else
          code[lc1].y := lc
      end (*ifstatement*);
            
      procedure repeatstatement;
      var
        x: item;
        lc1: integer;
      begin
        lc1 := lc;
        insymbol;
        statement([semicolon,untilsy]+fsys);
        while sy in [semicolon]+statbegsys do
        begin
          if sy = semicolon then
            insymbol
          else
            error(erpun);
          statement([semicolon,untilsy]+fsys)
        end;
        if sy = untilsy then
        begin
          insymbol;
          expression(fsys, x);
          if not (x.typ in [bools, notyp]) then
            error(ertyp);
          emit1(11,lc1)
        end
        else
          error(erkey)
      end (*repeatstatement*);
            
      procedure whilestatement;
      var
        x: item;
        lc1,lc2: integer;
      begin
        insymbol;
        lc1 := lc;
        expression(fsys+[dosy], x);
        if not (x.typ in [bools,notyp]) then
          error(ertyp);
        lc2 := lc;
        emit(11);
        if sy = dosy then
          insymbol
        else
          error(erkey);
        statement(fsys);
        emit1(10,lc1);
        code[lc2].y := lc
      end (*whilestatement*);
            
      procedure forstatement;
      var
        cvt: types;
        x: item;
        i,f,lc1,lc2: integer;
      begin
        insymbol;
        if sy = ident then
        begin
          i := loc(id);
          insymbol;
          if i = 0 then
            cvt := ints
          else
            if tab[i].obj = variable then
            begin
              cvt := tab[i].typ;
              emit2(0, tab[i].lev, tab[i].adr);
              if not (cvt in [notyp,ints,bools,chars]) then
                error(ertyp)
            end
            else
            begin
              error(ertyp);
              cvt := ints
            end
        end
        else
          skip([becomes,tosy,dosy]+fsys, erid);
        if sy = becomes then
        begin
          insymbol;
          expression([tosy,dosy]+fsys, x);
          if x.typ <> cvt then
            error(ertyp)
        end
        else
          skip([tosy,dosy]+fsys, erpun);
        if sy = tosy then
        begin
          insymbol;
          expression([dosy]+fsys, x);
          if x.typ <> cvt then
            error(ertyp)
        end
        else
          skip([dosy]+fsys, erkey);
        lc1 := lc; 
        emit(14);
        if sy = dosy then 
          insymbol
        else
          error(erkey);
        lc2 := lc; 
        statement(fsys);
        emit1(15,lc2); 
        code[lc1].y := lc
      end (*forstatement*);
      
      procedure standproc(n: integer);
      var i,f: integer;
        x,y: item;
      begin
        case n of
          1,2: 
          begin (*read*)
            if sy = lparent then 
            begin
              repeat
                insymbol;
                if sy <> ident then
                  error(erid)
                else
                begin
                  i := loc(id);
                  insymbol;
                  if i <> 0 then
                    if tab[i].obj <> variable then
                      error(ertyp)
                    else
                    begin
                      x.typ := tab[i].typ;
                      x.ref := tab[i].ref;
                      if tab[i].normal then
                        f := 0
                      else
                        f := 1;
                      emit2(f, tab[i].lev, tab[i].adr);
                      if sy = lbrack then
                        selector(fsys+[comma,rparent], x);
                      if x.typ in [ints,chars,notyp] then
                        emit1(27, ord(x.typ))
                      else
                        error(ertyp)
                    end
                end;
                test([comma,rparent],fsys, erkey);
              until sy <> comma;
              if sy = rparent then
                insymbol
              else
                error(erpun)
            end;
            if n = 2 then
              emit(62)
          end;
          3,4:
          begin (*write*)
            if sy = lparent then 
            begin
              repeat
                insymbol;
                if sy = string then
                begin
                  emit1(24,sleng);
                  emit1(28,inum);
                  insymbol
                end
                else
                begin
                  expression(fsys+[comma,colon,rparent], x);
                  if not (x.typ in stantyps) then
                    error(ertyp);
                  emit1(29,ord(x.typ))
                end
              until sy <> comma;
              if sy = rparent then
                insymbol
              else
                error(erpun)
            end;
            if n = 4 then emit(63)
          end;
          5,6:
            if sy <> lparent then
              error(erpun)
            else
            begin
              insymbol;
              if sy <> ident then
                error(erid)
              else
              begin
                i:= loc(id);
                insymbol;
                if i <> 0 then 
                  if tab[i].obj <> variable then
                    error(ertyp)
                  else
                  begin
                    x.typ:=tab[i].typ;
                    x.ref:=tab[i].ref;
                    if tab[i].normal then 
                      f:=0
                    else
                      f:=1;
                    emit2(f,tab[i].lev,tab[i].adr);
                    if sy=lbrack then
                      selector(fsys+[rparent],x);
                    if x.typ=ints then 
                      emit(n+1)
                    else
                      error(ertyp)
                  end
              end;
              if sy=rparent then
                insymbol
              else
                error(erpun)
            end;
        end;
      end (*standproc*);
            
    begin (*statement*)
      if sy in statbegsys+[ident] then 
        case sy of
          ident:
          begin
            i := loc(id);
            insymbol;
            if i <> 0 then
              case tab[i].obj of
                konstant, type1:
                  error(ertyp);
                variable:
                  assignment(tab[i].lev, tab[i].adr);
                prozedure:
                  if tab[i].lev <> 0 then
                    call(fsys, i)
                  else
                    standproc(tab[i].adr);
                funktion:
                  if tab[i].ref = display[level] then
                    assignment(tab[i].lev+1,0)
                  else
                    error(ertyp)
              end
            end;
          beginsy:
              if id='cobegin   ' then
              begin
                emit(4);
                compoundstatement;
                emit(5);
              end
              else
                compoundstatement;
          ifsy:
              ifstatement;
          whilesy:
              whilestatement;
          repeatsy:
              repeatstatement;
          forsy:
              forstatement;
        end;
      test(fsys, [], erpun)  
    end (*statement*);  
                 
  begin (*block*)
    dx := 5;
    prt := t;
    if level > lmax then
      fatal(5);
    test([lparent,colon,semicolon], fsys, erpun);
    enterblock;
    display[level] := b;
    prb := b;
    tab[prt].typ := notyp;
    tab[prt].ref := prb;
    if sy = lparent then
      parameterlist;
    btab[prb].lastpar := t;
    btab[prb].psize := dx;
    if isfun then
      if sy = colon then
      begin
        insymbol;    (*function type*)
        if sy = ident then
        begin
          x := loc(id);
          insymbol;
          if x <> 0 then
            if tab[x].obj <> type1 then
              error(ertyp)
            else
              if tab[x].typ in stantyps then
                tab[prt].typ := tab[x].typ
              else
                error(ertyp)
        end
        else
          skip([semicolon]+fsys, erid)
      end
      else
        error(erpun);
    if sy = semicolon then
      insymbol
    else
      error(erpun);
    repeat
      if sy = constsy then
        constantdeclaration;
      if sy = typesy then
        typedeclaration;
      if sy = varsy then
        variabledeclaration;
      btab[prb].vsize := dx;
      while sy in [proceduresy,functionsy] do
        procdeclaration;
      test([beginsy], blockbegsys+statbegsys, erkey)
    until sy in statbegsys;
    tab[prt].adr := lc;
    insymbol;
    statement([semicolon,endsy]+fsys);
    while sy in [semicolon]+statbegsys do
    begin
      if sy = semicolon then
        insymbol
      else
        error(erpun);
      statement([semicolon,endsy]+fsys)
    end;
    if sy = endsy then
      insymbol
    else
      error(erkey);
    test(fsys+[period], [], erkey)
  end (*block*);

  procedure interpret;
  label 97, 98;
  const
    stepmax = 8;  (*max steps before process switch*)
    tru = 1;  (*integer value of true*)
    fals = 0; (*integer value of false*)
    charl = 0; (*lowest character ordinal*)
    charh = 63; (*highest character ordinal*)
  type
    ptype = 0..pmax;  (*index over processes*)
  var
    ir: order;      (*instruction buffer*)
    ps: (run,fin,caschk,divchk,inxchk,stkchk,linchk,
         lngchk,redchk,deadlock);  (*processor status*)
    lncnt,                         (*number of lines*)
    chrcnt: integer;     (*number of characters in line*)
    h1,h2,h3,h4: integer; (*local variables*)
    s: array [1..stmax] of integer;     (*the stack*)

(*process table - one entry for each process*)
  ptab: array[ptype] of
    record
      t,b,                  (*top,bottom of stack*)
      pc,                       (*program counter*)
      stacksize: integer;           (*stack limit*)
      display: array[1..lmax] of integer;
      suspend: integer; (*0 or index of semaphore*)
      active: boolean     (*procedure active flag*)
    end;
  npr,
  curpr: ptype;
  stepcount: integer;
  seed: integer;
  pflag: boolean;  (*concurrent call flag*)
  
  procedure setran(seed:integer); extern;

  function ran: real; extern;

  procedure chooseproc;
  (*from a random starting point search for a process
    that is active and not suspended.  
    d aborts the interpreter if a deadlock occurs *)
  var
    d: integer;
  begin
    d:=pmax+1;
    curpr:=(curpr+trunc(ran*pmax))mod(pmax+1);
    while ((not ptab[curpr].active) or (ptab[curpr].suspend <> 0))
           and (d >= 0) do
    begin
      d:=d-1;
      curpr:=(curpr+1)mod(pmax+1)
    end;
    if d< 0 then
    begin
      ps:=deadlock;
      goto 98;
    end
    else
      stepcount:=trunc(ran*stepmax)
  end;

  function itob (i:integer): boolean;
  begin
    if i = tru then 
      itob:= true
    else
      itob:= false
  end;
  
  function btoi (b:boolean): integer;
  begin
    if b then 
      btoi:= tru
    else
      btoi:= fals
  end;

  begin (*interpret*)
    s[1] := 0;
    s[2] := 0;
    s[3] := -1;
    s[4] := btab[1].last;
    with ptab[0] do begin
      b:=0;
      suspend:=0;
      display[1]:=0;
      t:=btab[2].vsize-1;
      pc:=tab[s[4]].adr;
      active:=true;
      stacksize:=stmax-pmax*stkincr
    end;
    for curpr:=1 to pmax do
      with ptab[curpr] do
      begin
        active:=false;
        display[1]:=0;
        pc:=0;
        suspend:=0;
        b:=ptab[curpr-1].stacksize+1;
        stacksize:=b+stkincr-1;
        t:=b-1;
      end;
    npr:= 0;
    curpr:= 0;
    pflag:= false;
    seed:= clock;
    setran(seed); stepcount:= 0;
    ps:= run;
    lncnt:=0;
    chrcnt:=0;
    repeat
      if ptab[0].active then 
        curpr:= 0
      else
        if stepcount=0 then
          chooseproc
        else
          stepcount:=stepcount-1;
      with ptab[curpr] do
      begin 
        ir:= code[pc];
        pc:= pc+1;
      end;
      if pflag then
      begin
        if ir.f = 18 (*markstack*) then
          npr:=npr+1;
        curpr:=npr
      end;
      with ptab[curpr] do
        case ir.f of
        0: 
        begin (*load address*) 
          t := t+1;
          if t > stacksize then
            ps := stkchk
          else
            s[t] := display[ir.x] + ir.y
        end;
        1:
        begin (*load value*) 
          t := t+1;
          if t > stacksize then
            ps := stkchk
          else
            s[t] := s[display[ir.x] + ir.y]
        end;
        2:
        begin (*load indirect*)
          t := t+1;
          if t > stacksize then
            ps := stkchk
          else
            s[t] := s[s[display[ir.x] + ir.y]]
        end;
        3: 
        begin (*update display*)
          h1 := ir.y; 
          h2 := ir.x;
          h3 := b;
          repeat
            display[h1] := h3;
            h1 := h1-1;
            h3:= s[h3+2]
          until h1 = h2
        end;
        4: (*cobegin*) 
          pflag:=true;
        5: (*coend*)
        begin
          pflag:=false;
          ptab[0].active:=false
        end;
        6: (*wait*)
        begin
          h1:=s[t];
          t:=t-1;
          if s[h1] > 0 then
            s[h1]:=s[h1]-1
          else
          begin
            suspend:=h1;
            stepcount:=0;
          end
        end;
        7: (*signal*)
        begin
          h1:=s[t];
          t:=t-1;
          h2:=pmax+1;
          h3:=trunc(ran*h2);
          while (h2 >= 0) and (ptab[h3].suspend <> h1) do
          begin
            h3:=(h3+1) mod (pmax+1); 
            h2:=h2-1;
          end;
          if h2 < 0 then
            s[h1]:=s[h1]+1
          else
            ptab[h3].suspend:=0;
        end;
        8: 
          case ir.y of
            17:
            begin
              t:= t+1;
              if t > stacksize then
                ps := stkchk
              else
                s[t] := btoi(eof(input))
            end;
            18:
            begin
              t:= t+1;
              if t > stacksize then
                ps := stkchk
              else
                s[t] := btoi(eoln(input))
            end;
          end;
        10:
          pc := ir.y;   (*jump*)
        11: 
          begin (*conditional jump*)
            if s[t] = fals then
              pc := ir.y;
            t := t-1
          end;
        14:
          begin (*for1up*)
            h1 := s[t-1];
            if h1 <= s[t] then
              s[s[t-2]] := h1
            else
            begin
              t := t-3;
              pc := ir.y
            end
          end;
        15:
          begin (*for2up*) 
            h2 := s[t-2];
            h1:= s[h2] + 1;
            if h1 <= s[t] then
            begin
              s[h2] := h1;
              pc := ir.y
            end
            else
              t := t-3;
          end;
        18:
          begin (*mark stack*)
            h1 := btab[tab[ir.y].ref].vsize;
            if t+h1 > stacksize then
              ps := stkchk 
            else
            begin
              t := t+5;
              s[t-1] := h1-1;
              s[t] := ir.y
            end
          end;
        19:
          begin (*call*)
            h1 := t - ir.y;        (*h1 points to base*)
            h2 := s[h1+4];     (*h2 points to tab*)
            h3 := tab[h2].lev;
            display[h3+1] := h1;
            h4 := s[h1+3] + h1;
            s[h1+1] := pc;
            s[h1+2] := display[h3];
            s[h1+3] := b;
            for h3 := t+1 to h4 do
              s[h3] := 0;
            b := h1;
            t := h4;
            pc := tab[h2].adr
          end;
        21:
          begin (*index*)
            h1 := ir.y;      (*h1 points to atab*)
            h2 := atab[h1].low;
            h3 := s[t];
            if h3 < h2 then
              ps := inxchk
            else
              if h3 > atab[h1].high then
                ps := inxchk
              else
              begin
                t := t-1;
                s[t] := s[t] + (h3-h2)*atab[h1].elsize
              end
          end;
        22:
          begin (*load block*)
            h1 := s[t];
            t := t-1;
            h2 := ir.y + t;
            if h2 > stacksize then
              ps := stkchk
            else
              while t < h2 do
              begin
                t := t+1;
                s[t] := s[h1];
                h1 := h1+1
              end
          end;
        23: 
          begin (*copy block*)
            h1 := s[t-1];
            h2 := s[t];
            h3 := h1 + ir.y;
            while h1 < h3 do
            begin
              s[h1] := s[h2];
              h1 := h1+1;
              h2 := h2+1
            end;
            t := t-2
          end;
        24:
          begin (*literal*)
            t := t+1;
            if t > stacksize then
              ps := stkchk
            else
              s[t] := ir.y
          end;
        27:
          begin (*read*)
            if eof(input) then
              ps := redchk
            else
              case ir.y of
               1: read(s[s[t]]);
               3: 
                begin
                  read(ch); s[s[t]]:=ord(ch);
                end
              end;
            t := t-1
          end;
        28:
          begin (*write string*)
            h1 := s[t];
            h2 := ir.y;
            t := t-1;
            chrcnt := chrcnt+h1;
            if chrcnt > lineleng then
              ps := lngchk;
            repeat
              write(stab[h2]);
              h1 := h1-1;
              h2:= h2+1
            until h1 = 0
          end;
        29:
          begin (*write1*)
            if ir.y = 3 then
              h1:=1
            else
              h1:=10;
            chrcnt := chrcnt + h1;
            if chrcnt > lineleng then
              ps := lngchk
            else
              case ir.y of
               1: write(s[t]);
               2: write(itob(s[t]));
               3: if (s[t] < charl) or (s[t] > charh) then
                    ps:=inxchk
                  else
                    write(chr(s[t]))
              end;
            t := t-1
          end;
        31:
            ps := fin;
        32:
          begin
            t := b-1;
            pc := s[b+1];
            if pc <> 0 then
              b := s[b+3]
            else
            begin
              npr:=npr-1;
              active:=false;
              stepcount:=0;
              ptab[0].active := (npr=0)
            end
          end;
        33:
          begin (*exit function*)
            t := b;
            pc := s[b+1];
            b := s[b+3]
          end;
        34: s[t] := s[s[t]];
        35: s[t] := btoi(not(itob(s[t])));
        36: s[t] := - s[t];
        38: 
          begin (*store*)
            s[s[t-1]] := s[t];
            t := t-2
          end;
        45:
          begin
            t := t-1;
            s[t] := btoi(s[t] = s[t+1])
          end;
        46: 
          begin
            t := t-1;
            s[t] := btoi(s[t] <> s[t+1])
          end;
        47:
          begin
            t := t-1;
            s[t] := btoi(s[t] < s[t+1])
          end;
        48:
          begin
            t := t-1;
            s[t] := btoi(s[t] <= s[t+1])
          end;
        49:
          begin
            t := t-1;
            s[t] := btoi(s[t] > s[t+1])
          end;
        50:
          begin
            t := t-1;
            s[t] := btoi(s[t] >= s[t+1])
          end;
        51:
          begin
            t := t-1;
            s[t] := btoi(itob(s[t]) or itob(s[t+1]))
          end;
        52:
          begin
            t := t-1;
            s[t] := s[t] + s[t+1]
          end;
        53:
          begin
            t := t-1;
            s[t] := s[t] - s[t+1]
          end;
        56:
          begin
            t := t-1;
            s[t] := btoi(itob(s[t]) and itob(s[t+1]))
          end;
        57:
          begin
            t := t-1;
            s[t] := s[t] * s[t+1]
          end;
        58:
          begin
            t := t-1;
            if s[t+1] = 0 then
              ps := divchk
            else
              s[t] := s[t] div s[t+1]
          end;
        59:
          begin
            t := t-1;
            if s[t+1] = 0 then
              ps := divchk
            else
              s[t] := s[t] mod s[t+1]
          end;
        62:
            if eof(input) then
              ps := redchk
            else
              readln;
        63:
          begin
            writeln;
            lncnt := lncnt + 1;
            chrcnt := 0;
            if lncnt > linelimit then
              ps := linchk
          end
      end (*case*);
    until ps <> run;
 98:writeln;
    if ps <> fin then
    begin
      with ptab[curpr] do
        write('0halt at', pc:5, 'in process', curpr:4, ' because of ');
      case ps of
        deadlock: writeln('deadlock');
        divchk:   writeln('division by 0');
        inxchk:   writeln('invalid index');
        stkchk:   writeln('storage overflow');
        linchk:   writeln('too much output');
        lngchk:   writeln('line too long');
        redchk:   writeln('reading past end of file');
      end;
      writeln('0process  active  suspend  pc');
      for h1:= 0 to pmax do
        with ptab[h1] do
          writeln('0',h1:4,active,suspend,pc);
      writeln('0global variables');
      for h1:= btab[1].last+1 to tmax do
        with tab[h1] do 
          if lev <> 1 then
            goto 97
          else
            if obj = variable then
              if typ in stantyps then
                case typ of
                  ints:  writeln(name,' = ',s[adr]);
                  bools: writeln(name,' = ',itob(s[adr]));
                  chars: writeln(name,' = ',chr(s[adr] mod 64));
                end;
   97:writeln;
    end;
  end (*interpret*);

begin (*main*)
  message(' - concurrent pascal-s');
  key[ 1] := 'and       '; key[ 2] := 'array     ';
  key[ 3] := 'begin     '; key[ 4] := 'cobegin   ';
  key[ 5] := 'coend     '; key[ 6] := 'const     ';
  key[ 7] := 'div       '; key[ 8] := 'do        ';
  key[ 9] := 'else      '; key[10] := 'end       ';
  key[11] := 'for       '; key[12] := 'function  ';
  key[13] := 'if        '; key[14] := 'mod       ';
  key[15] := 'not       '; key[16] := 'of        ';
  key[17] := 'or        '; key[18] := 'procedure ';
  key[19] := 'program   '; key[20] := 'repeat    ';
  key[21] := 'then      '; key[22] := 'to        ';
  key[23] := 'type      '; key[24] := 'until     ';
  key[25] := 'var       '; key[26] := 'while     ';
  ksy[ 1] := andsy;        ksy[ 2] := arraysy;
  ksy[ 3] := beginsy;      ksy[ 4] := beginsy;
  ksy[ 5] := endsy;        ksy[ 6] := constsy;
  ksy[ 7] := idiv;         ksy[ 8] := dosy;
  ksy[ 9] := elsesy;       ksy[10] := endsy;
  ksy[11] := forsy;        ksy[12] := functionsy;
  ksy[13] := ifsy;         ksy[14] := imod;
  ksy[15] := notsy;        ksy[16] := ofsy;
  ksy[17] := orsy;         ksy[18] := proceduresy;
  ksy[19] := programsy;    ksy[20] := repeatsy;
  ksy[21] := thensy;       ksy[22] := tosy;
  ksy[23] := typesy;       ksy[24] := untilsy;
  ksy[25] := varsy;        ksy[26] := whilesy;
  sps['+'] := plus;        sps['-'] := minus;
  sps['('] := lparent;     sps[')'] := rparent;
  sps['='] := eql;         sps[','] := comma;
  sps['['] := lbrack;      sps[']'] := rbrack;
  sps['#'] := neq;         sps['&'] := andsy;
  sps[';'] := semicolon;   sps['*'] := times;
  constbegsys := [plus,minus,intcon,charcon,ident];
  typebegsys :=  [ident,arraysy];
  blockbegsys := [constsy,typesy,varsy,proceduresy,
                   functionsy,beginsy];
  facbegsys :=   [intcon,charcon,ident,lparent,notsy];
  statbegsys :=  [beginsy,ifsy,whilesy,repeatsy,forsy];
  stantyps :=    [notyp,ints,bools,chars];
  lc := 0;
  ll:=0;
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
  if sy <> programsy then
    error(erkey)
  else
  begin
    insymbol;
    if sy <> ident then
      error(erid)
    else
    begin
      progname := id;
      insymbol
    end
  end;
  enter('          ', variable, notyp, 0);  (*sentinel*)
  enter('false     ', konstant, bools, 0);              
  enter('true      ', konstant, bools, 1);              
  enter('char      ', type1, chars, 1);              
  enter('boolean   ', type1, bools, 1);              
  enter('integer   ', type1, ints , 1);              
  enter('eof       ', funktion, bools, 17);
  enter('eoln      ', funktion, bools, 18);              
  enter('read      ', prozedure, notyp, 1);              
  enter('readln    ', prozedure, notyp, 2);              
  enter('write     ', prozedure, notyp, 3);              
  enter('writeln   ', prozedure, notyp, 4);              
  enter('wait      ', prozedure, notyp, 5);              
  enter('signal    ', prozedure, notyp, 6);              
  enter('          ', prozedure, notyp, 0);
  with btab[1] do 
  begin
    last := t;
    lastpar := 1;
    psize := 0; 
    vsize := 0;
  end;
  block(blockbegsys+statbegsys, false, 1);
  if sy <> period then
    error(erpun);
  if btab[2].vsize > stmax-stkincr*pmax then
    7error(erln);
  emit(31); (*halt*)
  if not eof(input) then
    readln;
  if errs = [] then
    interpret
  else
    errormsg;
99: writeln;
end.