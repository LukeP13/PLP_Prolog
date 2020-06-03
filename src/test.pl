% not -> /+ (5<3)
% random -> random(0,5,X) #Random entre 0 i 5, que es guarda a X
% between -> between(0,10,X) #Tots els nombres entre 0 i 10
% succ -> succ(2, X) #Incrementa en 1 i assigna a X . X=3
% abs -> X is abs(-8) #Posa X = 8
% max(X, Y) o min(X,Y)
% round(X), truncate(X), floor(X)
% elevat -> 2 ** 3
% / divideix, // divideix i descarta decimals
% write, nl, writeq(per fer q es vegin les ''), format('~w ~s $~2f', [A, "hola", C]), put(X)--per un character
% read(X)--str entre '', get(X)--char

% -- Files --
% open(File, write, Stream),
% write(Stream, Text), nl,
% close(Stream)

write_to_file(File, Text) :-
  open(File, write, Stream),
  write(Stream, Text), nl,
  close(Stream).

read_file(File) :-
  open(File, read, Stream),
  get_char(Stream, Char1),
  process_stream(Char1, Stream),
  close(Stream).

process_stream(end_of_file, _) :- !.

process_stream(Char, Stream) :-
  write(Char),
  get_char(Stream, Char2),
  process_stream(Char2, Stream).

count_up(Low, High) :-
  between(Low, High, Y),
  write(Y), nl.

%%%% Llavor Cromàtic TRIA %%%%% OKK !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
invAbs(X, Y):- Y is X.
invAbs(X, Y):- Y is -X.

unitaria(F, Lit) :-
  member(H, F),
  length(H, 1),
  Lit is H.

% (Si trobem clàusules unitàries) Podriem escollir múltiples clàusules unitàries, però si una falla no arreglarem
%  el problema cambiant de clàusula unitària. Per tant si el primer falla, no agafarem els següents
tria(F, Lit) :-
  unitaria(F, X) ->
    % Si trobem la clàusula unitària l'escollim
    Lit is X;
    % Altrament, escollim el primer booleà o el seu negat
    [[P|_]|_] = F, invAbs(P, Lit).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test1(X) :- tria([[-1,5],[-2,3],[1,5,6,-2]], X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%% Simplify test %%%%%%
simplif(_, [], []) :- !.
simplif(Lit, [H|T], FS) :-
  simp_clausula(Lit, H, NewH) ->
    ([] = NewH ->
      % Si trobem la clàusula buida sortim, altrament afegim la modificada
      fail, !;
      % Altrament, simplifiquem la resta de clàusules i afegim la que hem reduït al principi
      simplif(Lit, T, X), FS = [NewH|X]
    );
    % Si no retorna clàusula simplificada, simplifiquem la resta
    simplif(Lit, T, FS).


simp_clausula(_, [], []) :- !.
simp_clausula(Lit, [H|T], LS) :-
  % Si trobem el nombre, fallà ja que s'elimina la clàusula
  Lit =\= H ->
    (Lit =:= -H ->
      % Si trobem el nombre en negat ja podrem
      LS = T;
      simp_clausula(Lit, T, X), LS = [H|X]
    ); fail, !.

test2(X) :- simplif(1,[[1,5]], X), !.
%[2,3],[1,5],[-2,3,-1],[1,5,6,-2]

%%%%%%% TEST SAT %%%%%%%%%%%% OKKK !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
sat([],I,I):-     write('SAT!!'),nl,!.
sat(CNF,I,M):-
   % Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
   tria(CNF,Lit),

   % Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
   simplif(Lit,CNF,CNFS),

   % crida recursiva amb la CNF i la interpretacio actualitzada
   sat(CNFS, [Lit|I], M).

testSat(X) :- sat([[1,2,3,4],[-1,-2],[-1,-3],[-1,-4],[-2,-3],[-2,-4],[-3,-4]], [], X).
testSat2(X) :- sat([[1],[2,-3, 4],[-2,3],[4,5],[-2,-3]], [], X).
testSat3(X) :- sat([[1],[2],[-2,-1]], [], X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%% UnCert Test  %%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% unCert(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
% ... pots crear i utilitzar els auxiliars comaminimUn i nomesdUn
unCert(L, CNF) :-
  comaminimUn(L,X),
  nomesdUn(L, Y),
  append(X,Y,CNF).

%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
% ...
comaminimUn(L,[L]) :- !.

%%%%%%%%%%%%%%%%%%%
% nomesdUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
% Per codificar aquest CNF agafarem totes les possibles combinacions de parelles de nombres de L en negatiu.
% Forma: [[-H,-T1],[-H,-T2]]..
nomesdUn([], []) :- !.
nomesdUn([H|T],CNF) :-
  nomesdUn(T, X),
  invertNums([H|T], [Hneg|Tneg]),
  creaCombi(Hneg, Tneg, Combi),
  append(Combi, X, CNF).

%%%%%%%%%%%%%%%%%%%
% invertNums(L, LS)
% Donat una llista de variables booleanes,
% -> el segon parametre serà la llista amb els elements negats
invertNums([], []) :- !.
invertNums([H|T], [Hinv|Tinv]) :-
  Hinv is -H,
  invertNums(T, Tinv).

%%%%%%%%%%%%%%%%%%
% creaCombi(N, L, LS)
% Donat una variable booleana i una llista de variables booleanes
% -> El tercer paràmetre sera la llista amb totes les possibles combinacions
creaCombi(_, [], []) :- !.
creaCombi(N, [H|T], [[N,H]|F]) :- creaCombi(N, T, F).


%%%%%%%%%%%%
testUn1(X) :- unCert([1,2,3,4], X).
testUn2(X) :- unCert([1,2,3,4], Y), sat(Y, [], X).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
