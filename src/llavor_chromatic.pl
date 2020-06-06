
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
    [[P|_]|_] = F, invAbs(P, Lit).


%%%%%%%%%%%%%%%%%%%%%
% unitaria(F, Lit)
% Donat uana CNF,
% -> El segon parametre qualsevol de les clàusules unitàries
unitaria(F, Lit) :-
  member(H, F),
  length(H, 1),
  Lit is H.

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
%
%
inicialitza(_, [], []) :- !.

%Afegim el color que ens demana com a clàusula unitaria per assegurar que es cumplirà
inicialitza(LLV, [(N, Color)|T], [[NColor]|CNF]) :-
    %Agafem la Llista del color que toca dins LLV
    nth1(N, LLV, LV),

    %Agafem el primer valor
    nth1(Color, LV, NColor),

    %Creem el cnf per els seguents vertex
    inicialitza(LLV, T, CNFresta),

    %Creem la llista on només 1 pugui ser cert
    unCert(LV, CNFun),

    %Unim les llistes
    append(CNFun, CNFresta, CNF).

%--------------------------------- DONE FINS AQUI ----------------------------------%

%%%%%%%%%%%%%%%%%%%
% els nodes del graph son nombres consecutius d'1 a N.
% K es el nombre de colors a fer servir.
% Arestes es la llista d'arestes del graph com a parelles de nodes
% Inici es la llista de parelles (node,num_color) que s'han de forçar
% C sera la CNF que codifica graph coloring problem pel graph donat
codifica(N,K,Arestes,Inici,C):-!.
   %crear la llista de llistes de variables pels colors de cada node
   %crear la CNF que fa que cada node tingui un color
   %crear la CNF que força els colors dels nodes segons Inici
   %crear la CNF que fa que dos nodes que es toquen tinguin colors diferents
   %C sera el resultat d'ajuntar les CNF creades



%%%%%%%%%%%%%%%%%%%%
% resolGraf(N,A,K,Inputs)
% Donat el nombre de nodes, el nombre de colors, les Arestes A, i les inicialitzacions,
% -> es mostra la solucio per pantalla si en te o es diu que no en te.

resol(N,K,A, I):-
   codifica(...),
   write('SAT Solving ..................................'), nl,
   %crida a SAT
   write('Graph (color number per node in order: '), nl
   %mostrar el resultat
   .


%%%%%%%%%%%%%%%%%%%%
% chromatic(N,A,Inputs)
% Donat el nombre de nodes,  les Arestes A, i les inicialitzacions,
% -> es mostra la solucio per pantalla si en te o es diu que no en te.
% Pista, us pot ser util fer una inmersio amb el nombre de colors permesos.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% com a query podeu cridar:
% ?- graf1(N,A), chromatic(N,A,[]).
% i aixi amb altres grafs que us definiu com els que hi ha a continuacio:


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
