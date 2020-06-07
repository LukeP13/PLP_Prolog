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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% DYNAMICS %%%%%%%%%
:- dynamic(trobat/1).
:- dynamic(mode/1).

trobat(solucio).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%% Llavor Cromàtic TRIA %%%%% OKK !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
invAbs(X, Y):- Y is X.
invAbs(X, Y):- Y is -X.

unitaria(F, Lit) :-
  member(H, F),
  length(H, 1),
  [Lit|_] = H.

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


%------------------------------------------ TESTED -------------------------------------------------%


% LLV -> [[1,2,3],[4,5,6],[7,8,9]]
% Ini -> [(n, color)|T]
% CNF -> [[1],[1,2],[unCert]...]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% inicialitza(LLV, Ini, CNF)
%
%
inicialitza(_, [], []) :- !.

%Afegim el color que ens demana com a clàusula unitaria per assegurar que es cumplirà
inicialitza(LLV, [(N, Color)|T], [[NColor]|CNF]) :-
    %Agafem la Llista del color que toca dins LLV
    nth1(N, LLV, LV),

    %Agafem el valor que pertoca a Color (Xij)
    nth1(Color, LV, NColor),

    %Creem el cnf per els seguents vertex
    inicialitza(LLV, T, CNF).


testInic(X) :- inicialitza([[1,2,3],[4,5,6],[7,8,9]],[(1,3),(2,2),(3,2)],X).




%------------------------------------------ TESTED -------------------------------------------------%
%%%%%%%%%%%%%%%%%%%%%
% seguent(LA, O, S)
% Donat una llista d'arestes LA i un punt origen O:
% -> S és qualsevol dels següents vèrtex als quals podem anar
seguent(LA, O, S) :-
  member((I, F), LA),
  inside(O, S, I, F).

inside(O, S, O, S).
inside(O, S, S, O).

hasColor([], _, _) :- !, fail.
hasColor([(V, Color)|_], V, Color) :- !.
hasColor([(V, _)|T], V, Color) :- !, fail.
hasColor([(VS, N)|T], V, Color) :- hasColor(T, V, Color).


numArestes(V, L, Count) :- aggregate_all(count, seguent(L, V, Seg), Count), !.


segColorList([], _, _, []) :- !.
segColorList(_, [], _, []) :- !.
segColorList(LS, [(A, B)|T], N, RES) :-
  inside(A, B, N, Seg),
  hasColor(LS, Seg, C), !,
  segColorList(LS, T, N, LSeg),
  RES = [C|LSeg].


segColorList(LS, [(A, B)|T], N, LSeg) :- segColorList(LS, T, N, LSeg).


firstNotIn(L, N, Max, X) :- length(L, Len), N > Len+1, !, fail.
firstNotIn(L, N, Max, Res) :-
  member(N, L), !,
  NS is N+1,
  firstNotIn(L, NS, Max, Res).

firstNotIn(L, N, _, N) :- mode(oneSolution), !.
firstNotIn(L, N, _, N). %% Otherwise
firstNotIn(L, N, M, X) :- NS is N+1, firstNotIn(L, NS, M, X).


creaArestes(0, Max, Arestes, []) :- !.
creaArestes(N, Max, Arestes, L) :-
  mode(normal),
  NS is N-1, !,
  creaArestes(NS, Max, Arestes, LS),
  segColorList(LS, Arestes, N, LSeg),
  firstNotIn(LSeg, 1, Max, Color),
  L = [(N, Color)|LS].

creaArestes(N, Max, Arestes, L) :-
  mode(fast),
  NS is N-1, !,
  creaArestes(NS, Max, Arestes, LS),
  segColorList(LS, Arestes, N, LSAux),
  sort(LSAux, LSeg), % Eliminem els duplicats
  firstNotIn(LSeg, 1, Max, Color),
  L = [(N, Color)|LS].

creaArestes(N, Max, Arestes, L) :-
  mode(totes),
  NS is N-1, !,
  creaArestes(NS, Max, Arestes, LS),
  segColorList(LS, Arestes, N, LSeg),
  firstNotIn(LSeg, 1, Max, Color),
  L = [(N, Color)|LS].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesMutexes(LLV, Arestes, CNF)
%
fesMutexes(LLV, Arestes, CNF) :-
  length(LLV, N),
  creaArestes(N, N, Arestes, LS),
  inicialitza(LLV, LS, CNF).

%%%%
testMutexes(X) :- fesMutexes([[1,2],[3,4],[5,6]],[(1,3),(2,3)],X).
%%%%

llista(F, F, []) :- !.
llista(I, F, [I|LS]) :-
  IS is I+1,
  llista(IS, F, LS).

creaLLV(0, _, I, I) :- !.
creaLLV(N, K, LLS, I) :-
  Ini is ((N-1)*K)+1,
  Fi is Ini+K,
  llista(Ini, Fi, L),
  NS is N-1,
  creaLLV(NS, K, [L|LLS], I).


null_output_sat(F, L, I) :-
  open_null_stream(Out),
  tell(Out),
  sat(F, L, I), told.


%%%%%%
testCod(X) :- codifica(3,2,[(1,3),(2,3)],[], X).
%%%%%%


%---------------------------------------------------------------------------------------------------------%
llistaUnCert([], []) :- !.
llistaUnCert([L|LT], CNF) :-
  unCert(L, FA),
  llistaUnCert(LT, FS),
  append(FA, FS, CNF), !.


append3(A, B, C, Res) :-
  append(A, B, Aux),
  append(Aux, C, Res).

%%%%%%%%%%%%%%%%%%%
% els nodes del graph son nombres consecutius d'1 a N.
% K es el nombre de colors a fer servir.
% Arestes es la llista d'arestes del graph com a parelles de nodes
% Inici es la llista de parelles (node,num_color) que s'han de forçar
% C sera la CNF que codifica graph coloring problem pel graph donat
codifica(N,K,Arestes,Inici,C):-
   %crear la llista de llistes de variables pels colors de cada node
   creaLLV(N, K, [], LLV),

   %crear la CNF que fa que cada node tingui un color
   llistaUnCert(LLV, CNFU),

   %crear la CNF que força els colors dels nodes segons Inici
   inicialitza(LLV, Inici, CNFI),

   %crear la CNF que fa que dos nodes que es toquen tinguin colors diferents
   fesMutexes(LLV, Arestes, CNFD),

   %C sera el resultat d'ajuntar les CNF creades
   append3(CNFU, CNFI, CNFD, C).


%%%%%%%%%%%%%%%%%%%%
% resolGraf(N,A,K,Inputs)
% Donat el nombre de nodes, el nombre de colors, les Arestes A, i les inicialitzacions,
% -> es mostra la solucio per pantalla si en te o es diu que no en te.
resol(N,K,A, I):- !,
   codifica(N, K, A, I, C),
   write('SAT Solving ..................................'), nl,
   sat(C, [], Sol),
   format('Nombre cromatic = ~w', [K]), nl,
   write('Vertex per color: '), nl,
   %mostrar el resultat
   mostraSol(Sol, K, 1)
   .


setMode(102) :- not(mode(fast)), asserta(mode(fast)), setMode(102).
setMode(102) :- write('-- MODE FAST --'), nl, !.

setMode(120) :- not(mode(fast)), asserta(mode(fast)), setMode(120).
setMode(120) :- not(mode(oneSolution)), asserta(mode(oneSolution)), setMode(120).
setMode(120) :- write('-- MODE UNA SOLUCIO --'), nl, !.

setMode(116) :- not(mode(totes)), asserta(mode(totes)), setMode(116).
setMode(116) :- write('--- BUSCANT TOTES LES SOLUCIONS, JO EM FARIA UN CAFE... ---'), nl, !.

setMode(110) :- not(mode(normal)), asserta(mode(normal)), setMode(110).
setMode(110) :- write('--- MODE NORMAL ---'), nl, !.

setMode(X) :- write('Invalid key '), put(X), write(' choose another one'), nl, fail.

%%%%%%%%%%%%%%%%%%%%
% chromatic(N,A,Inputs)
% Donat el nombre de nodes,  les Arestes A, i les inicialitzacions,
% -> es mostra la solucio per pantalla si en te o es diu que no en te.
% Pista, us pot ser util fer una inmersio amb el nombre de colors permesos.
chromatic(N, A, Inputs) :- trobat(solucio), retract(trobat(solucio)), !, chromatic(N, A, Inputs).
chromatic(N, A, Inputs) :-
  retractall(mode(_)),
  write('Choose mode (n: normal | t: totes | f: fast | x: oneSolution) -> '),
  get_single_char(Mode), nl, format('~w', [Mode]),
  setMode(Mode), !,
  iChromatic(N, 1, A, Inputs).


iChromatic(N, K, _, _) :- N < K, !, write('\n!!! No sha trobat solucio !!!'), !, fail.
iChromatic(N, K, A, I) :- resol(N, K, A, I), asserta(trobat(solucio)).
iChromatic(N, K, A, I) :- not(trobat(solucio)), KS is K+1, iChromatic(N, KS, A, I).

%---------------------------------------------------------------------------------------------------------%

%%%%%%%%%%%%%%%%%%%%
% mostraSol(Sol, Max, N)
% Donada una Solució i un nombre de colors:
% -> Mostra la solució per pantalla
% -> Utilitza
mostraSol(_, Max, N) :- Max < N, !.
mostraSol(Sol, Max, N) :-
  % Mostrem el color N
  format('color ~w: ', [N]),

  % Mostrem tots els Vèrtex que son del color N
  mostraVertex(Sol, N, Max), !,

  %Mostrem el següent color
  NS is N+1,
  mostraSol(Sol, Max, NS).


%%%%%%%%%%%%%%%%%%%%
% mostraSol(Sol, Max, N)
% Donada una Solució i un nombre de colors:
% -> Mostra la solució per pantalla
% -> Utilitza
mostraVertex([], _, _) :- nl, !.

mostraVertex([C|LC], Color, Max) :-
  C > 0,
  Color-1 =:= (C-1) mod Max,
  V is (C-1)//Max + 1,
  format(' ~w ',[V]),
  mostraVertex(LC, Color, Max).

mostraVertex([_|LC], Color, Max) :- mostraVertex(LC, Color, Max).


%%%%%%
test1() :- chromatic(3,[(1,3),(2,3)],[(1,1)]).
tR() :- chromatic(8, [(1,2),(1,3),(2,5),(5,1)], []).
test2() :- graf1(N, A), chromatic(N, A, []).
test3() :- graf2(N, A), chromatic(N, A, []).
test4() :- graf3(N, A), chromatic(N, A, []).
t2(X) :- chromatic(10,[(1,2),(2,3),(3,4),(4,5),(5,1),(1,6),(2,7),(3,8),(4,9),(5,10),(6,8),(7,9),(8,10),(9,6),(10,7)],[]).


% aquest graf te 21 nodes i nombre chromatic 4.
graf1(11,[(1,2),(1,4),(1,7),(1,9),(2,3),(2,6),(2,8),(3,5),(3,7),(3,10),
         (4,5),(4,6),(4,10),(5,8),(5,9),(6,11),(7,11),(8,11),(9,11),(10,11)]).

% aquest graf te 23 nodes i nombre chromatic 5.
graf2(23,[(1,2),(1,4),(1,7),(1,9),(1,13),(1,15),(1,18),(1,20),(2,3),(2,6),(2,8),(2,12),(2,14),(2,17),(2,19),
         (3,5),(3,7),(3,10),(3,13),(3,16),(3,18),(3,21),(4,5),(4,6),(4,10),(4,12),(4,16),(4,17),(4,21),
         (5,8),(5,9),(5,14),(5,15),(5,19),(5,20),(6,11),(6,13),(6,15),(6,22),(7,11),(7,12),(7,14),(7,22),
         (8,11),(8,13),(8,16),(8,22),(9,11),(9,12),(9,16),(9,22),(10,11),(10,14),(10,15),(10,22),
         (11,17),(11,18),(11,19),(11,20),(11,21),(12,23),(13,23),(14,23),(15,23),(16,23),(17,23),
         (18,23),(19,23),(20,23),(21,23),(22,23)]).



graf3(25,
      [(1,7),(1,5),(1,6),(1,11),(1,16),(1,21),(2,8),(2,14),(2,20),(2,6),(2,3),(2,4),(2,5),(2,7),(2,1),
      (3,9),(3,15),(3,7),(3,2),(3,1),(4,10),(4,8),(4,12),(4,16),(4,5),(4,9),(4,14),(4,19),
      (4,24),(4,3),(4,2),(4,1),(5,9),(5,13),(5,17),(5,21),(5,10),(5,15),(5,1),
      (6,12),(6,18),(6,24),(6,7),(6,8),(6,9),(6,10),(6,11),(6,16),(6,21),(6,2),(6,1),
      (7,13),(7,19),(7,25),(7,11),(7,8),(7,6),(7,3),(7,2),(7,1),(8,14),(8,20),
      (8,12),(8,16),(8,9),(8,7),(8,6),(8,4),(8,3),(8,2),(9,15),(9,13),(9,17),(9,21),
      (9,10),(9,14),(9,19),(9,24),(9,8),(9,7),(9,6),(9,5),(9,4),(9,3),(10,14),(10,18),
      (10,22),(10,15),(10,20),(10,25),(10,9),(10,8),(10,7),(10,6),(10,5),(10,4),
      (11,17),(11,23),(11,12),(11,13),(11,7),(12,16),(12,13),(12,14),(12,15),(12,17),
      (12,22),(12,4),(12,2),(13,19),(13,25),(13,17),(13,21),(13,14),(13,15),(13,18),
      (13,23),(13,12),(13,3),(13,1),(14,20),(14,18),(14,9),(14,8),(14,4),(14,2),(15,19),
      (15,23),(15,20),(15,25),(15,14),(15,13),(15,12),(15,11),(15,10),(15,9),(15,5),
      (15,3),(16,22),(16,17),(16,18),(16,19),(16,20),(16,21),(16,12),(16,11),(16,8),
      (16,6),(17,19),(17,20),(17,22),(17,16),(17,13),(17,12),(17,11),(17,9),(17,7),(17,5),
      (17,2),(18,24),(18,22),(18,19),(18,16),(18,14),(18,13),(18,12),(18,10),(18,8),(18,6),
      (19,24),(19,18),(19,17),(19,16),(19,15),(19,14),(19,13),(19,9),(19,7),(19,4),(19,1),
      (20,24),(20,25),(20,19),(20,18),(20,17),(20,16),(20,15),(20,14),(20,10),(20,8),(20,5),
      (20,2),(21,22),(21,5),(21,1),(22,23),(22,24),(22,25),(22,14),(22,12),(22,10),(22,7),
      (22,2),(23,24),(23,25),(23,22),(23,21),(23,19),(23,18),(23,17),(23,15),(23,13),(23,11),
      (23,8),(23,3),(24,25),(24,23),(24,22),(25,24),(25,23),(25,13)]).
%%%%%%


%
