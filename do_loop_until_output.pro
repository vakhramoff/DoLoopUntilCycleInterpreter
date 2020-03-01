DOMAINS
    text = string
    list_str = string*
    list_char = char*
    l_text = list_str*
    int_val = integer
    int_list = int_val*

DATABASE
    db_lexem(text)
    db_symint_vall(text)
    db_const(text)
    db_ident(text)
    db_prog(text)
    db_i_symint_vall(text)
    db_i_keyword(text)
    db_prog_code(list_str)
    
    db_ident_impl(text, integer)
    db_mem(text, integer)

PREDICATES
    fill_dbs_of_lexems_specs_keywords
    lex_analyse
    syntax_analyse
    program_solution_and_implementation
    spec_s_helper
    ident_initialize
    prog_impl
    stop_and_show_values_of_variables
    
    implement_opers(l_text)
    text_read(text)
    check(text)
    num(list_str)
    alp(list_str)
    calc_av(list_str)
    blo(text)
    os(text)
    ao(text)
    op(text)
    vs(list_str)
    lv(list_str)
    av(list_str)
    opers(list_str)
    oper(list_str)
    ident_impl_add_helper(list_str)
    show_value_helper(list_str)
    
    lv_priority(text, integer)
    ao_priority(text, integer)
    spec_s(text, integer)
    elem(text, list_str)
    numeric(text, text)
    const_ident(text, text)
    const_ident_helper(text, text)
    last_elem(list_str, text)
    get_chars(text, list_str)
    calc_lv(list_str, list_str)
    what(text, integer)
    vars_shower_helper(list_str, int_list)
    get_spacedb_str(text, text)
    
    str_prepare(text, text, text)
    prepare(list_str, text, text, text)
    read_helper(text, text, integer)
    con(list_str, list_str, list_str)
    con_extended(l_text, l_text, l_text)
    calc_lv_first_priority(list_str, list_str, list_str)
    calc_lv_second_priority_first_round(list_str, list_str, list_str)
    calc_lv_second_priority_second_round(list_str, list_str, list_str)
    take_opers(list_str, l_text, l_text)
    division(int_val, int_val, int_val)
    run_while(list_str, list_str, list_str)
    get_chars_helper(text, list_str, list_str)
    calc_av_second_priority(list_str, list_str, list_str)
    calc_av_first_priority(list_str, list_str, list_str)
    
    trim_list(list_str, text, list_str, list_str)
    
    trim_list_helper(list_str, text, list_str, list_str, list_str)

CLAUSES
    opers(T) :- oper(T), !.
    opers(T) :- trim_list(T,";",X,Y),!, oper(X), opers(Y),!.
    
    oper(["input",X|T]) :- T=[], db_ident(X), !.
    oper(["output",X|T]) :- T=[], op(X), !.
    oper([X,"="|T]) :- db_ident(X), av(T),!.
    
    blo(X) :- X="and"; X="or".
    
    os(X) :- X="<"; X=">"; X="="; X="<>".
    
    ao(X) :- X="+"; X="-"; X="*";  X="/".
    
    lv_priority(X,I) :- X="and", I=1 ; X="or", I=1;
        X="=", I=2 ; X="<", I=2; X=">", I=2; X="<>", I=2.
    ao_priority(X,I) :- X="+", I=1 ; X="-", I=1; X="*", I=2; X="/", I=2.
    
    num(X) :- X=["0","1","2","3","4","5","6","7","8","9"].
    alp(X) :- X=["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q",
                    "r","s","t","u","v","w","x","y","z","A","B","C","D","E","F","G",
                    "H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W",
                    "X","Y","Z"].
    
    fill_dbs_of_lexems_specs_keywords :-  assertz(db_i_symint_vall("+")), 
            assertz(db_i_symint_vall("-")),
            assertz(db_i_symint_vall("*")),
            assertz(db_i_symint_vall("/")),
            assertz(db_i_symint_vall("=")),
            assertz(db_i_symint_vall("<")),
            assertz(db_i_symint_vall(">")),
            assertz(db_i_symint_vall("<>")),
            assertz(db_i_symint_vall(";")),
            assertz(db_i_keyword("do")),
            assertz(db_i_keyword("loop")),
            assertz(db_i_keyword("until")),
            assertz(db_i_keyword("input")),
            assertz(db_i_keyword("output")),
            assertz(db_i_keyword("and")),
            assertz(db_i_keyword("or")).
            
    op(X) :- db_ident(X),! ; db_const(X),!.
    
    vs([X|W]) :- op(X),W=[],!.
    vs([X,Y,Z|W]) :- op(X),os(Y),op(Z),W=[],!.
    
    lv(X) :- vs(X), !.
    lv(T) :- blo(X),trim_list(T,X,Y,Z),vs(Y), lv(Z).
    
    av([X]) :- op(X), !.
    av(T) :- ao(X), trim_list(T,X,Y,Z), av(Y), av(Z).
    
    
    trim_list(Z,H,Y,X) :- trim_list_helper(Z,H,[],Y,X).
    trim_list_helper([H|Z],H,Y,Y,Z).
    trim_list_helper([H|T],X,Y,G,Z) :- X<>H, con(Y,[H],Y1), trim_list_helper(T,X,Y1,G,Z).
    
    con([],L,L).
    con([X|L1], L2,[X|L3]):-con(L1, L2, L3).
    
    con_extended([],L,L).
    con_extended([X|L1], L2,[X|L3]):-con_extended(L1, L2, L3).
    
    last_elem([T],T).
    last_elem([_|H],T) :- last_elem(H,T).
    
    elem(X,[X|_]).
    elem(X,[_|T]):-elem(X,T).
    
    prepare([],_,X,X).
    prepare([X|T],C,Acc,Z) :- not(X=C), concat(Acc,X,Acc1), prepare(T,C,Acc1,Z) ; X=C, get_spacedb_str(C, C2), concat(Acc,C2,Acc1), prepare(T,C,Acc1,Z).
    
    get_spacedb_str(X,R) :- concat(X," ",R1), concat(" ",R1,R).
    
    get_chars(X,E):-get_chars_helper(X,[],E).
    get_chars_helper("",E,E).
    get_chars_helper(X,E,R) :- frontstr(1,X,H,T), con(E,[H],E1), get_chars_helper(T,E1,R).
    
    str_prepare(X, C, R) :- get_chars(X, Q), prepare(Q, C, "", R).
    
    division(_,0,R) :- R = 0, !.
    division(X, Y, R) :- M = X mod Y, R = (X - M) div Y, !.
    
    ident_initialize :- findall(X, db_ident(X), X_OUTPUT), ident_impl_add_helper(X_OUTPUT),!.
    
    what(X,Y) :- db_ident_impl(X,Y),! ; str_int(X,Y),!.
    
    text_read(X) :- concat(X," ",Z),
                        str_prepare(Z,"=",W1),
                        str_prepare(W1,"+",W2),
                        str_prepare(W2,"-",W3),
                        str_prepare(W3,"*",W4),
                        str_prepare(W4,"/",W5),
                        str_prepare(W5,";",W6),
                    read_helper(W6,"",0).%, not(err(_)).
    
    read_helper("",_,_) :- !.
    read_helper(X,Y,K) :- frontstr(1, X, H, E), spec_s(H,K), check(Y), T=K+1, read_helper(E,"",T), spec_s_helper,!.
    read_helper(X,Y,K) :- frontstr(1, X, H, E), concat(Y,H,S), T=K+1, read_helper(E,S,T), spec_s_helper,!.
    
    spec_s(_,X) :- db_mem(T,X), db_i_symint_vall(T), assertz(db_prog(T)),!.
    spec_s(X,K) :- X="<",assertz(db_mem(X,K)),assertz(db_prog("<")),!.
    spec_s(" ",_) :- !.
    spec_s(X,K) :- X=">", T=K-1, db_mem("<",T), db_i_symint_vall(X), not(db_symint_vall(X)),assertz(db_symint_vall("<>")),
                    assertz(db_prog("<>")), retract(db_mem("<",T)), retract(db_prog("<")),!.
    spec_s(X,_) :- X=">",assertz(db_prog(X)),!.
    spec_s(X,_) :- db_i_symint_vall(X), assertz(db_prog(X)), not(db_symint_vall(X)), assertz(db_symint_vall(X)),!.
    
    spec_s_helper :- db_mem(X,_), not(db_symint_vall(X)), assertz(db_symint_vall(X)), retractall(db_mem(_,_)), !.
    spec_s_helper.
    
    check(X) :- X="", !; X=" ", !.
    check(X) :- db_i_keyword(X),assertz(db_prog(X)),assertz(db_lexem(X)), !.
    check(X) :- numeric(X,X), !.
    check(X) :- const_ident(X,X), !.
    
    numeric(X,Y) :- frontstr(1,X,E,Z), num(F), elem(E,F), numeric(Z,Y), !.
    numeric("",Y) :- assertz(db_const(Y)), assertz(db_prog(Y)).
    
    const_ident(X,Y) :- frontstr(1,X,E,Z),alp(F), elem(E,F), const_ident_helper(Z,Y), !.
    const_ident(_,_).
    
    const_ident_helper(X,Y) :- frontstr(1,X,E,Z), alp(F), elem(E,F), const_ident_helper(Z,Y),!; frontstr(1,X,E,Z), num(F), elem(E,F), const_ident_helper(Z,Y),!.
    const_ident_helper("",Y) :- db_ident(Y), assertz(db_prog(Y)), !.
    const_ident_helper("",Y) :- assertz(db_ident(Y)),assertz(db_prog(Y)). 
    
    run_while(X,Y,K) :- calc_av(X), calc_lv(Y,["F"]), run_while(X,Y,K),!.
    run_while(_,Y,K) :- calc_lv(Y,["T"]), K=["T"].
    
    ident_impl_add_helper([]).
    ident_impl_add_helper([Q|W]) :- assertz(db_ident_impl(Q,0)), ident_impl_add_helper(W),!.
        
    implement_opers([]).
    implement_opers([H|T]) :- H=[D,"="|Ty], calc_av_first_priority(Ty,[],Q), calc_av_second_priority(Q,[],[X|_]), retractall(db_ident_impl(D,_)), str_int(X,XX), assertz(db_ident_impl(D,XX)), implement_opers(T), !.
    implement_opers([H|T]) :- H=["output",E], show_value_helper([E]),implement_opers(T),!.
    implement_opers([H|T]) :- H=["input",E], write("Enter the value of ["),write(E),write("]: "),readln(Reply), retractall(db_ident_impl(E,_)),str_int(Reply,G), assertz(db_ident_impl(E,G)), implement_opers(T), !.
                                    
    show_value_helper([]).
    show_value_helper([X|T]) :- findall(Y, db_ident_impl(X,Y), Y_OUTPUT), Y_OUTPUT = [Q|_],
                    write(X),write(" = "),write(Q), nl,show_value_helper(T).
    
    take_opers([],X,X).
    take_opers(T,R,Y) :- con(Head,[";"|U],T), con_extended(R,[Head],RR), take_opers(U,RR,Y),!.
    take_opers(T,R,Y) :- con_extended(R,[T],RR), take_opers([],RR,Y),!.
    
    calc_av(T) :-
        take_opers(T,[],K), implement_opers(K),!.
    
    calc_av_first_priority([],X,X).
    calc_av_first_priority([Q|[]],Z,H) :- con(Z,[Q],ZZ),calc_av_first_priority([],ZZ,H).
    calc_av_first_priority([Q,"*",E|[]],Z,H) :-
        what(Q,QQ), what(E,EE), F = QQ*EE, str_int(A,F), con(Z,[A],ZZ),calc_av_first_priority([],ZZ,H), !.
    calc_av_first_priority([Q,"/",E|[]],Z,H) :-
        what(Q,QQ), what(E,EE), division(QQ,EE,F), str_int(A,F), con(Z,[A],ZZ),calc_av_first_priority([],ZZ,H), !.
    calc_av_first_priority([Q,"*",E|Tail],Z,H) :-
        what(Q,QQ), what(E,EE), F = QQ*EE, str_int(A,F), con([A],Tail,R), calc_av_first_priority(R,Z,H), !.
    calc_av_first_priority([Q,"/",E|Tail],Z,H) :-
        what(Q,QQ), what(E,EE), division(QQ,EE,F), str_int(A,F) , con([A],Tail,R), calc_av_first_priority(R,Z,H), !.
    calc_av_first_priority([Q,P|Tail],Z,H) :- ao_priority(P,1), con(Z,[Q,P],ZZ),calc_av_first_priority(Tail,ZZ,H),!.
        
    calc_av_second_priority([T],_,[X]):-
        what(T,TT), str_int(X,TT), !.
    calc_av_second_priority([Q,"+",E|[]],_,H) :-
        what(Q,QQ), what(E,EE), F=QQ+EE, str_int(A,F), calc_av_second_priority([],[A],H), !.
    calc_av_second_priority([Q,"-",E|[]],_,H) :-
        what(Q,QQ), what(E,EE), F=QQ-EE, str_int(A,F), calc_av_second_priority([],[A],H), !.
    calc_av_second_priority([Q,"+",E|Tail],Z,H) :-
        what(Q,QQ), what(E,EE), F=QQ+EE, str_int(A,F), con([A],Tail,R), calc_av_second_priority(R,Z,H), !.
    calc_av_second_priority([Q,"-",E|Tail],Z,H) :-
        what(Q,QQ), what(E,EE), F=QQ-EE, str_int(A,F), con([A],Tail,R), calc_av_second_priority(R,Z,H), !.
    
    calc_lv(X,Z) :- calc_lv_first_priority(X,[],Y), calc_lv_second_priority_first_round(Y,[],T), calc_lv_second_priority_second_round(T,[],Z), !.
    
    calc_lv_first_priority([],X,X).
    calc_lv_first_priority([Q,"<",E|[]],Z,H) :-
        what(Q,QQ), what(E,EE), QQ<EE, con(Z,["T"],R), calc_lv_first_priority([],R,H), ! ;
        con(Z,["F"],R), calc_lv_first_priority([],R,H), !.
    calc_lv_first_priority([Q,">",E|[]],Z,H) :-
        what(Q,QQ), what(E,EE), QQ>EE, con(Z,["T"],R), calc_lv_first_priority([],R,H), ! ;
        con(Z,["F"],R), calc_lv_first_priority([],R,H), !.
    calc_lv_first_priority([Q,"<>",E|[]],Z,H) :- what(Q,QQ), what(E,EE), QQ<>EE, con(Z,["T"],R), calc_lv_first_priority([],R,H), ! ;
        con(Z,["F"],R), calc_lv_first_priority([],R,H), !.
    calc_lv_first_priority([Q,"=",E|[]],Z,H) :- what(Q,QQ), what(E,QQ), con(Z,["T"],R), calc_lv_first_priority([],R,H), ! ;
        con(Z,["F"],R), calc_lv_first_priority([],R,H), !.
    calc_lv_first_priority([T],Z,X):-
        what(T,TT), TT<>0, con(Z,["T"],X),! ;
        con(Z,["F"],X),!. 
    calc_lv_first_priority([Q,">",E,Lop|Tail],Z,H) :-
        what(Q,QQ), what(E,EE), QQ>EE, con(Z,["T",Lop],R), calc_lv_first_priority(Tail,R,H), ! ;
        con(Z,["F",Lop],R), calc_lv_first_priority(Tail,R,H), !.
    calc_lv_first_priority([Q,"<",E,Lop|Tail],Z,H) :-
        what(Q,QQ), what(E,EE), QQ<EE, con(Z,["T",Lop],R), calc_lv_first_priority(Tail,R,H), ! ;
        con(Z,["F",Lop],R), calc_lv_first_priority(Tail,R,H), !.
    calc_lv_first_priority([Q,"<>",E,Lop|Tail],Z,H) :- what(Q,QQ), what(E,EE), QQ<>EE, con(Z,["T",Lop],R), calc_lv_first_priority(Tail,R,H), ! ;
        con(Z,["F",Lop],R), calc_lv_first_priority(Tail,R,H), !.
    calc_lv_first_priority([Q,"=",E,Lop|Tail],Z,H) :- what(Q,QQ), what(E,QQ), con(Z,["T",Lop],R), calc_lv_first_priority(Tail,R,H), ! ;
        con(Z,["F",Lop],R), calc_lv_first_priority(Tail,R,H), !.
    calc_lv_first_priority([Q,"and"|Tail],Z,H) :- what(Q,QQ), QQ<>0, con(Z,["T","and"],R), calc_lv_first_priority(Tail,R,H), ! ;
        con(Z,["F","and"],R), calc_lv_first_priority(Tail,R,H), !.
    calc_lv_first_priority([Q,"or"|Tail],Z,H) :- what(Q,QQ), QQ<>0, con(Z,["T","or"],R), calc_lv_first_priority(Tail,R,H), ! ;
        con(Z,["F","or"],R), calc_lv_first_priority(Tail,R,H), !.
        
    calc_lv_second_priority_first_round([T],X,R) :- con(X,[T],R),!.
    calc_lv_second_priority_first_round([Q,"and",E|Tail],Z,H) :- 
        Q="T", E="T", con(["T"],Tail,NTail), calc_lv_second_priority_first_round(NTail,Z,H),!;
        con(["F"],Tail,NTail), calc_lv_second_priority_first_round(NTail,Z,H), !.
    calc_lv_second_priority_first_round([Q,"or"|Tail],Z,H) :-
        con(Z,[Q,"or"],ZZ),calc_lv_second_priority_first_round(Tail,ZZ,H),!.
    calc_lv_second_priority_second_round([],X,X). % calc(X,[Y|_]), result = Y
    calc_lv_second_priority_second_round([T],X,R) :- con(X,[T],R),!.
    calc_lv_second_priority_second_round([Q,"or",E|Tail],Z,H) :- 
        Q="F", E="F", con(["F"],Tail,NTail), calc_lv_second_priority_second_round(NTail,Z,H),!;
        con(["T"],Tail,NTail), calc_lv_second_priority_second_round(NTail,Z,H), !.
    
    lex_analyse :- findall(X, db_prog(X), OUTPUT), assertz(db_prog_code(OUTPUT)).
    syntax_analyse :- db_prog_code(OUTPUT), OUTPUT=["do"|T], trim_list(T,"loop",Q,[U|I]), U="until", opers(Q), lv(I).
    program_solution_and_implementation :- db_prog_code(OUTPUT), OUTPUT=["do"|T], trim_list(T,"loop",Q,[U|I]), U="until", run_while(Q,I,_).
    
    stop_and_show_values_of_variables :- findall(X, db_ident_impl(X,Y), X_OUTPUT),findall(Y, db_ident_impl(X,Y), Y_OUTPUT),
                                        write("__________________________________________________"),nl,nl,
                                        write("          Variables values after program implementation:"),nl,nl,
                                        vars_shower_helper(X_OUTPUT,Y_OUTPUT),
                                        write("__________________________________________________"),nl,nl.
    
    vars_shower_helper([],_).
    vars_shower_helper([Q|W],[E|R]) :- write("          "),
                                       write(Q),
                                       write(" = "),
                                       write(E),
                                       nl, vars_shower_helper(W,R).
    
    prog_impl :- lex_analyse,
                 syntax_analyse,
                 ident_initialize,
                 program_solution_and_implementation,
                 stop_and_show_values_of_variables.

GOAL
    fill_dbs_of_lexems_specs_keywords,
        SOURCE_CODE = "do a = a + 7; n = n + 7; b = a * n + 7 - 64 / n; output a; output n; output b loop until n > 40 and 7 or 3 or 0 or a > 345 and b > 1000000",
    text_read(SOURCE_CODE),
    prog_impl.