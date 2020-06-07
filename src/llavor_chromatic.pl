%%%%%%%%%%%%%%%%%%% AUTORS %%%%%%%%%%%%%%%%%%%
%     Lluc Pagès Pérez        u1953628       %
%    Joel Carrasco Mora       u1955382       %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%% DYNAMICS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Utilitzarem els dynamics per modificar aspectes
% en temps d'execució:
% -> trobat(solucio): ens dirà si hem trobat la solució
% -> mode/1: modificarem el mode d'execució que volem

:- dynamic(trobat/1).
:- dynamic(mode/1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretacio I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.
sat([],I,I):-     write('SAT!!'),nl,!.
sat(CNF,I,M):-
   % Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
   tria(CNF,Lit),

   % Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
   simplif(Lit,CNF,CNFS),

   % crida recursiva amb la CNF i la interpretacio actualitzada
   sat(CNFS, [Lit|I], M).


%%%%%%%%%%%%%%%%%%
% tria(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
%
% (Si trobem clàusules unitàries)
%  -> Podriem escollir múltiples clàusules unitàries, però si la primera falla no arreglarem
%     el problema cambiant de clàusula unitària. Per tant només comprovarem el primer trobat.
%
% (Si no trobem clàusula unitària)
%  -> Triarem el primer booleà o el seu negat
tria(F, Lit) :-
  unitaria(F, X) ->
    % Si trobem la clàusula unitària l'escollim
    Lit is X;
    % Altrament, escollim el primer booleà o el seu negat
    [[P|_]|_] = F,
    invAbs(P, Lit)
    .


%%%%%%%%%%%%%%%%%%%%%
% unitaria(F, Lit)
% Donat uana CNF,
% -> El segon parametre es qualsevol de les clàusules unitàries
unitaria(F, Lit) :-
  member(H, F),
  length(H, 1),
  [Lit|_] = H.

%%%%%%%%%%%%%%%%%%%%%
% invAbs(X, Y)
% Donat un nombre en valor absolut X,
% -> El segon parametre sera qualsevol dels valors en positiu o negatiu de tal nombre
%
% Ens permet obtenir un nombre en positiu i negatiu
invAbs(X, Y):- Y is X.
invAbs(X, Y):- Y is -X.


%%%%%%%%%%%%%%%%%%%%%
% simlipf(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
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


%%%%%%%%%%%%%%%%%%%%%
% simp_clausula(Lit, L, LS)
% Donada una literal Lit i una clàusula
% -> El tercer parametre sera la clàusula simplificada:
%   - Fallarà si troba la clàusula
%   - Eliminarà el -Lit si el troba, aqui pot aparèixer la clàusula buida
simp_clausula(_, [], []) :- !.
simp_clausula(Lit, [H|T], LS) :-
  % Si trobem el nombre, fallà ja que s'elimina la clàusula
  Lit =\= H ->
    (Lit =:= -H ->
      % Si trobem el nombre en negat ja podrem
      LS = T;
      simp_clausula(Lit, T, X), LS = [H|X]
    ); fail, !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%
% unCert(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
% ... pots crear i utilitzar els auxiliars comaminimUn i nomesdUn
unCert(L, CNF) :-
  comaminimUn(L,X),
  nomesdUn(L, Y),
  append(X,Y,CNF).

%%%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
% Unicament hem de ficar aquesta llista dins una altra llista, aixo creara un sat amb minim
%  un valor de L positiu.
comaminimUn(L,[L]) :- !.

%%%%%%%%%%%%%%%%%%%%%
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% inicialitza(LLV, Ini, CNF)
% Donat una llista de LLV i una llista dels colors a inicialitzar:
% -> El tercer parametre es el CNF que fa que es compleixin els colors

inicialitza(_, [], []) :- !. % Aturem inmersio

%Afegim el color que ens demana com a clàusula unitaria per assegurar que es cumplirà
inicialitza(LLV, [(N, Color)|T], [[NColor]|CNF]) :-
    %Agafem la Llista del color que toca dins LLV
    nth1(N, LLV, LV),

    %Agafem el valor que pertoca a Color (Xij)
    nth1(Color, LV, NColor),

    %Creem el cnf per els seguents vertex
    inicialitza(LLV, T, CNF)
    .


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% inside(Aresta, O, S)
% Donada una aresta i un vèrtex origen O:
% -> Diu si el vertex forma part de l'Aresta i retorna el seguent
inside((O, S), O, S).
inside((O, S), S, O).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% hasColor(LC, V, Color)
% Donada una llista de colors LC, un vèrtex V:
% -> El tercer parametre és el color del vertex V dins LC
hasColor([], _, _) :- !, fail.
hasColor([(V, Color)|_], V, Color) :- !.
hasColor([(V, _)|T], V, Color) :- !, fail.
hasColor([(VS, N)|T], V, Color) :- hasColor(T, V, Color).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% segColorList(LS, Arestes, N, LSeg)
% Donada una llista de parelles (Vertex, Color), una llista de arestes
% i un Vertex V:
% -> L'ultim parametre és la llista de colors dels seguents vèrtex de V

% Frenem Inmersio
segColorList([], _, _, []) :- !.
segColorList(_, [], _, []) :- !.

% Si V forma part d'Aresta
segColorList(LS, [Aresta|T], V, [C|LSeg]) :-
  % Comprovem que el vèrtex estigui dins l'aresta
  inside(Aresta, V, Seg),

  % Agafem el color del Seguent
  hasColor(LS, Seg, C), !,

  % Comprovem el resta d'arestes
  segColorList(LS, T, V, LSeg)
  .

% Si el Vertex no forma part d'Aresta seguim buscant
segColorList(LS, [_|T], V, LSeg) :- segColorList(LS, T, V, LSeg).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% firstNotIn(L, N, Max, X)
% Donada una llista de colors, un N inicial i un Màxim de color:
% -> El quart paràmetre és el color escollit (El primer que està lliure)
%%%%%
% **** MODES ****
%
% - OneSolution: Tallarem al primer nombre trobat, donarà la resposta mes
%                ràpida, però no ens assegura trobar solució, ni ferho amb
%                el mínim nombre chromatic
%
% - Otherwise: Tallarem al superar la longitud de L, que és el nombre d'arestes
%              (o colors diferents).
%

% Tallem les possibles solucions
firstNotIn(L, N, Max, X) :- length(L, Len), N > Len+1, !, fail.

% Part principal - Si N és dins L, busquem el seguent
firstNotIn(L, N, Max, Res) :-
  member(N, L), !,
  NS is N+1,
  firstNotIn(L, NS, Max, Res)
  .

% Si hem trobat un no "membre" el retornem
firstNotIn(L, N, _, N) :- mode(oneSolution), !. % Mode OneSolution
firstNotIn(L, N, _, N).                         % Otherwise

% Tot i que sigui membre, també podriem trobar altres colors possibles
firstNotIn(L, N, M, X) :- NS is N+1, firstNotIn(L, NS, M, X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% triaColors(N, Max, Arestes, L)
% Donat un nombre de vertex, un maxim de colors i una llista d'Arestes:
% -> l'últim paràmetre és una llista de parelles de (vertex, color) tal que
%    cada vertex tingui un color diferent als seus adjacents
%
%  **** MODES ****
%
%  - Fast: El color dels vertex pot arribar com a màxim al nombre de
%          colors diferents dels seus adjacents
%

% Amb 0 vèrtex tenim 0 colors, para inmersio
triaColors(0, Max, Arestes, []) :- !.

% MODE FAST
triaColors(N, Max, Arestes, [(N, Color)|LS]) :-
  % Comprovem que estigui en mode fast
  mode(fast),

  % Triem els colors dels seguents vertex
  NS is N-1, !,
  triaColors(NS, Max, Arestes, LS),

  % Creem la llista de colors dels vèrtex seguents
  segColorList(LS, Arestes, N, LSAux),

  % Eliminem els duplicats
  sort(LSAux, LSeg),

  % Triem un color
  firstNotIn(LSeg, 1, Max, Color)
  .

% ----------------------------------------------------------------------%;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% parellsUnCert(LA, LB, CNF)
%
parellsUnCert([], _, []) :- !.
parellsUnCert(_, [], []) :- !.

parellsUnCert([LA|TA], [LB|TB], CNF) :-
  nomesdUn([LA, LB], F),
  parellsUnCert(TA, TB, FS),
  append(F, FS, CNF).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% totesMutexes(LLV, Arestes, CNF)
%
%

totesMutexes(_, [], []) :- !.

totesMutexes(LLV, [(A, B)|LA], CNF) :-
  nth1(A, LLV, AL),
  nth1(B, LLV, BL),
  parellsUnCert(AL, BL, F),
  totesMutexes(LLV, LA, FS),
  append(F, FS, CNF).

% ----------------------------------------------------------------------%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesMutexes(LLV, Arestes, CNF)
% Donat un LLV (Llista de llistes de booleans)
% i una llista de arestes:
% -> El tercer parametre sera un CNF que evita que dos veins comparteixin color

fesMutexes(LLV, Arestes, CNF) :-
  % Busquem el nombre de Nodes que tenim (igual a la longitud de LLV)
  length(LLV, N),

  (mode(totes) ->
    totesMutexes(LLV, Arestes, CNF);

    (% Creem la llista de colors per a cada vèrtex
    triaColors(N, N, Arestes, LS),

    % Creem el CNF amb els colors trobats
    inicialitza(LLV, LS, CNF)
    )
  ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% llista(Inici, Fi, L)
% Donat una nombre Inici i un Fi:
% -> el tercer parametre sera la llista [Inici .. Fi-1]

llista(F, F, []) :- !. % Si els nombres son iguals

% Afegim el nombre al inici de la llista
llista(I, F, [I|LS]) :-
  IS is I+1,
  llista(IS, F, LS). % Inmersio


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% creaLLV(LLT, LLV)
% Donat un nombre de vertex, i un nombre de vectors
% -> el tercer paràmetre l'anirem actualitzant
% -> el quart paràmetre serà el LLV resultant

% Quan arribem a 0, assignem el resultat
creaLLV(0, _, I, I) :- !.

creaLLV(N, K, LLS, I) :-
  % Busquem el nombre Inici i Fi de la llista per el color N
  Ini is ((N-1)*K)+1,
  Fi is Ini+K,

  % Creem una llista de [Inici .. Fi-1]
  llista(Ini, Fi, L),

  % Inmersió amb el seguent vèrtex
  NS is N-1,
  creaLLV(NS, K, [L|LLS], I).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% llistaUnCert(LLV, CNF)
% Donat una llista de llistes de booleans:
% -> el segon paràmetre serà el cnf resultant
%
% Crida a la funció unCert per totes les llistes de l'LLV

llistaUnCert([], []) :- !. % Aturem Inmersio

llistaUnCert([L|LT], CNF) :-
  % Cridem a unCert per la llista actual
  unCert(L, FA),

  % Busquem les seguents
  llistaUnCert(LT, FS),

  % Ajuntem el resultat
  append(FA, FS, CNF), !
  .


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% append3(A, B, C, Res)
% Donat 3 llistes:
% -> Res serà el resultat de unirles totes en ordre A-B-C.
append3(A, B, C, Res) :-
  append(A, B, Aux),
  append(Aux, C, Res).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% codifica(N,K,Arestes,Inici,C)
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



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% resolGraf(N,A,K,Inputs)
% Donat el nombre de nodes, el nombre de colors, les Arestes A, i les inicialitzacions,
% -> es mostra la solucio per pantalla si en te o es diu que no en te.
resol(N,K,A, I):- !,
  %Codifiquem el graf amb K colors
  codifica(N, K, A, I, C),

  % Busquem la solucio amb el SAT solver
  write('SAT Solving ..................................'), nl,
  sat(C, [], Sol),

  % Mostrem el nombre chromatic i la solucio
  format('Nombre cromatic = ~w', [K]), nl,
  write('Vertex per color: '), nl,
  mostraSol(Sol, K, 1)
  .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% setMode(Mode)
% Modes: 116-totes, 102-fast, 120-oneSolution.
% Donat un caràcter ASCII:
% -> "activa" el mode en concret

%% Mode FAST %%
setMode(102) :- not(mode(fast)), asserta(mode(fast)), setMode(102).
setMode(102) :- write('-- MODE FAST --'), nl, !.

%% Mode OneSolution %%
setMode(120) :- not(mode(fast)), asserta(mode(fast)), setMode(120).
setMode(120) :- not(mode(oneSolution)), asserta(mode(oneSolution)), setMode(120).
setMode(120) :- write('-- MODE UNA SOLUCIO --'), nl, !.

%% Mode Totes %%
setMode(116) :- not(mode(totes)), asserta(mode(totes)), setMode(116).
setMode(116) :- write('--- BUSCANT TOTES LES SOLUCIONS, JO M\'ANIRIA A FER UN CAFE... ---'), nl, !.

%% Lletra Invàlida %%
setMode(X) :- write('Invalid key '), put(X), write(' choose another one'), nl, fail.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% chromatic(N,A,Inputs)
% Donat el nombre de nodes,  les Arestes A, i les inicialitzacions,
% -> es mostra la solucio per pantalla si en te o es diu que no en te.
% Pista, us pot ser util fer una inmersio amb el nombre de colors permesos.
chromatic(N, A, Inputs) :-
  % Eliminem tots els modes, i la "solucio trobada"
  retractall(trobat(_)),
  retractall(mode(_)),

  % L'usuari escull el mode
  write('Choose mode ( t: totes | f: fast | x: oneSolution ) -> '),
  get_single_char(Mode), nl,
  setMode(Mode), !,

  % Resolem el problema
  time(iChromatic(N, 1, A, Inputs)),

  % Si hem escollit "una solucio" solució, acabem
  (mode(oneSolution) -> !; nl)
  .



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% iChromatic(N, K, A, I)
% Funció inmersiva de chromatic/3, busca el nombre chromatic

% Comprovem que el nombre K no sigui més gran de N, si ho és fallem.
iChromatic(N, K, _, _) :-
  N < K,
  write('\n!!! No sha trobat solucio !!!'),
  !, fail
  .

% Resolem el graph amb nombre cromàtic K, i si el trobem diem "solucio trobada"
iChromatic(N, K, A, I) :-
  resol(N, K, A, I),
  asserta(trobat(solucio)) % "Solucio trobada!"
  .

% En cas de haver fallat, busquem amb el nombre cromàtic K+1
iChromatic(N, K, A, I) :-
  not(trobat(solucio)),
  KS is K+1,
  iChromatic(N, KS, A, I) % Inmersio
  .


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% mostraSol(Sol, Max, N)
% Donada una Solució i un nombre de colors:
% -> Mostra la solució per pantalla
% Per a Cada color mostra els vertex assignats
mostraSol(_, Max, N) :- Max < N, !.
mostraSol(Sol, Max, N) :-
  % Mostrem el color N
  format('color ~w: ', [N]),

  % Mostrem tots els Vèrtex que son del color N
  mostraVertex(Sol, N, Max), !,

  % Mostrem el següent color
  NS is N+1,
  mostraSol(Sol, Max, NS)
  .


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% mostraVertex(Sol, Color, N)
% Donada una Solució i un color:
% -> Mostra els vèrtex que tenen aquell color per pantalla

mostraVertex([], _, _) :- nl, !. % Aturem la cerca

mostraVertex([C|LC], Color, Max) :-
  % Comprovem que C sigui Color, i guardem a V el vèrtex
  C > 0,
  Color-1 =:= (C-1) mod Max,
  V is (C-1)//Max + 1,

  % Mostrem Vertex
  format(' ~w ',[V]),
  mostraVertex(LC, Color, Max) % Inmersio
  .

mostraVertex([_|LC], Color, Max) :- mostraVertex(LC, Color, Max). % Inmersio


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% genera(K, Arestes, N)
% Donat un nombre cromàtic K:
% -> El segon paràmetre son les arestes del graf generat
% -> El tercer paràmetre son el nombre d'arestes del graf
genera(K, Arestes, N) :-
  iGenera(K, K, Arestes, N), !.

%%%%%%%%%%%%%%%%
% iGenera(V, Max, Arestes, N)
% Funció inmersiva del genera
iGenera(0, _, [], 0) :- !.
iGenera(V, Max, A, Max) :-
  % Genera els seguents
  VS is V-1,
  iGenera(VS, Max, AS, NS),

  % Genera les combinacions amb nombre V
  combinacions(V, Max, AW),

  % Uneix els resultats
  append(AS, AW, A)
  .

%%%%%%%%%%%%%%%%%
% combinacions(Ini, Fi, L)
% Donat un nombre Inici i un Fi:
% -> El tercer paràmetre es una llista de parelles de combinacions
%
% Exemple: [(Ini, Ini+1), (Ini, Ini+2) .. (Ini, Fi)]
%
combinacions(Ini, Fi, []) :- Ini >= Fi, !.

combinacions(Ini, Fi, [(Ini, Fi)|CS]) :-
  FS is Fi - 1,
  combinacions(Ini, FS, CS)
  .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% com a query podeu cridar:
% ?- graf1(N,A), chromatic(N,A,[]).
% i aixi amb altres grafs que us definiu com els que hi ha a continuacio:

% graf 0 %
graf0(3, [(1,2),(2,3)]).

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

graf4(10,[(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),
        (2,10),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(5,6),(5,7),
        (5,8),(5,9),(5,10),(6,7),(6,8),(6,9),(6,10),(7,8),(7,9),(7,10),(8,9),(8,10),(9,10)]).

graf5(20,
      [(1,20),(1,19),(1,18),(1,17),(1,16),(1,15),(1,14),(1,13),(1,12),(1,11),(1,10),(1,9),(1,8),(1,7),(1,6),(1,5),
      (1,4),(1,3),(1,2),(2,20),(2,19),(2,18),(2,17),(2,16),(2,15),(2,14),(2,13),(2,12),(2,11),(2,10),(2,9),(2,8),
      (2,7),(2,6),(2,5),(2,4),(2,3),(3,20),(3,19),(3,18),(3,17),(3,16),(3,15),(3,14),(3,13),(3,12),(3,11),(3,10),
      (3,9),(3,8),(3,7),(3,6),(3,5),(3,4),(4,20),(4,19),(4,18),(4,17),(4,16),(4,15),(4,14),(4,13),(4,12),(4,11),
      (4,10),(4,9),(4,8),(4,7),(4,6),(4,5),(5,20),(5,19),(5,18),(5,17),(5,16),(5,15),(5,14),(5,13),(5,12),(5,11),
      (5,10),(5,9),(5,8),(5,7),(5,6),(6,20),(6,19),(6,18),(6,17),(6,16),(6,15),(6,14),(6,13),(6,12),(6,11),(6,10),
      (6,9),(6,8),(6,7),(7,20),(7,19),(7,18),(7,17),(7,16),(7,15),(7,14),(7,13),(7,12),(7,11),(7,10),(7,9),(7,8),
      (8,20),(8,19),(8,18),(8,17),(8,16),(8,15),(8,14),(8,13),(8,12),(8,11),(8,10),(8,9),(9,20),(9,19),(9,18),(9,17),
      (9,16),(9,15),(9,14),(9,13),(9,12),(9,11),(9,10),(10,20),(10,19),(10,18),(10,17),(10,16),(10,15),(10,14),(10,13),
      (10,12),(10,11),(11,20),(11,19),(11,18),(11,17),(11,16),(11,15),(11,14),(11,13),(11,12),(12,20),(12,19),(12,18),
      (12,17),(12,16),(12,15),(12,14),(12,13),(13,20),(13,19),(13,18),(13,17),(13,16),(13,15),(13,14),(14,20),(14,19),
      (14,18),(14,17),(14,16),(14,15),(15,20),(15,19),(15,18),(15,17),(15,16),(16,20),(16,19),(16,18),(16,17),(17,20),
      (17,19),(17,18),(18,20),(18,19),(19,20)])
