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

%%%% Llavor Cromàtic TRIA %%%%% OK
unitaria(F, Lit) :-
  member(H, F),
  length(H, 1) -> Lit is H.

tria(F, Lit) :-
  %Iterem sobre tots els mebres de F
  unitaria(F, X) ->
    Lit is X;
    [[Lit|_]|_] = F.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test1(X) :- tria([[-1,5],[-2,3],[1,5,6,-2]], X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%% Simplify test %%%%%%
simplif(_, [], FS) :- FS = [], !.
simplif(Lit, [H|T], FS) :-
  simp_clausula(Lit, H, NewH) ->
    simplif(Lit, T, X), FS = [NewH|X];
    simplif(Lit, T, FS).

simp_clausula(_, [], LS) :- LS = [], !.
simp_clausula(Lit, [H|T], LS) :-
  Lit =\= H ->
    (Lit =:= -H ->
      LS = T;
      simp_clausula(Lit, T, X), LS = [H|X]
    ).


test2(X) :- simplif(1,[[-1,5],[2,3],[1,5],[-2,3],[1,5,6,-2]], X), !.
%[-1,5],[1,5],[-2,3],[1,5,6,-2]
