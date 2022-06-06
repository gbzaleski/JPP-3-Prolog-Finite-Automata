% Grzegorz B. Zaleski (418494)

% Załadowanie modułu.
:- use_module(library(lists)).

% Sprawdza czy podany automat jest poprawny, jeśli tak to zwraca jego reprezentacje.
% correct(+Automat, -Reprezentacja) -> automatum(Alphabet, Vertices, Edges, Start, Ends, Reachable).
correct(dfa(Edges, Start, EndsRaw), Repr) :-
    % Sprawdza czy automat jest ustalony a zmienna dla reprezentacji wolna.
    ground(Edges), \+ var(Start), ground(EndsRaw), var(Repr),

    % Sprawdza brak powtórzen w liście wierzchołków akceptowanych.
    allUnique(EndsRaw),

    % Tworzy reprezentacje automatu.
    getAlphabet(Edges, AlphabetRaw),
    AlphabetRaw \= [],
    getVertices(Edges, [Start | EndsRaw], VerticesRaw),
    sort(VerticesRaw, Vertices),
    sort(AlphabetRaw, Alphabet),
    sort(EndsRaw, Ends),

    cartesianProduct(Alphabet, Alphabet, Vertices, Product),
    cutDestination(Edges, CutEdges),
    sort(Product, SortedProduct),
    sort(CutEdges, CutEdgesSorted),

    % Warunek całkowitości funkcji przejścia i niedetermistyczności.
    CutEdgesSorted == SortedProduct,
    length(Edges, EdgesSize),
    length(CutEdgesSorted, EdgesSize),

    % Szuka wierzchołków z których nie ma drogi do stanu akceptującego.
    getReachable(Edges, Ends, ReachableRaw),
    sort(ReachableRaw, Reachable),

    % Użycie struktury zbilansowanego drzewa BST.
    constructBST(Reachable, ReachableTree),
    constructBST(Ends, EndsTree),

    Repr = automatum(Alphabet, Vertices, Edges, Start, EndsTree, ReachableTree).

% Reprezentacja automatu zawiera 6 atrybutów:
% Alphabet - Alfabet nad którym automat buduje słowa
% Vertices - Zbiór stanów (wierzchołków) automatu
% Edges - Deterministyczna i całkowita funkcja przejścia (krawędzie przejść)
% Start - Stan (wierzchołek) początkowy
% Ends - Zbiór stanów (wierzchołków) akceptujących (końcowych).
% Reachable - Zbiór stanów z których da się dojśc do stanu akceptującego.
% Dzięki takiej strukturze danych wszystkie problemy udało się rozwiązać w
%   czasie wielomianowym - w przeciwieństwie do brutalnego rozwiązania
%   wykładniczego, czasami zastosowano nawet kolejne optymalizacje jak np.
%   sprawdzenie poprawności funkcji poprzez iloczyn kartezjański, który
%   zbił złożonoć z O(n^3) do O(n^2), sprawdzenie elementu przed
%   wrzuceniem ich na strukture przy BFS-ie/DFS-ie, czy zastosowanie
%   zbilansowanego drzewa BST.

% Sprawdza unikalność elementów na liście.
allUnique(Lst) :-
    sort(Lst, Sorted),
    length(Lst, OriginalLength),
    length(Sorted, SortedLength),
    OriginalLength == SortedLength.

% Pobiera alfabet z listy przejść.
getAlphabet([], []).
getAlphabet([fp(_, C, _) | T], [C | Alphabet]) :- getAlphabet(T, Alphabet).

% Pobiera wierzchołki (stany) automatu z listy przejść.
getVertices([], Acc, Acc).
getVertices([fp(A, _, B) | T], Acc, R) :- getVertices(T, [A, B | Acc], R).

% Tworzy zbiór krawędzi, bez drugiego końca.
cutDestination([], []).
cutDestination([fp(From, C, _) | TEdges], [(From, C) | CutEdges]) :-
    cutDestination(TEdges, CutEdges).

% Produkt kartezjański wszystkich liter i wierzchołków.
cartesianProduct(_Alphabet, _, [], []).
cartesianProduct(Alphabet, [], [_V | TVertices], Result) :-
    cartesianProduct(Alphabet, Alphabet, TVertices, Result).
cartesianProduct(Alphabet, [C | Letters], [V | TVertices], [(V, C) | Result]) :-
    cartesianProduct(Alphabet, Letters, [V | TVertices], Result).

% Wylicza osiągalne stany, (używa krawędzi odwrotnie).
getReachable(Edges, Currents, Reachable) :-
    nextLayer(Edges, Currents, [], NextLayer),
    append(NextLayer, Currents, NewCurrents),
    (NextLayer == [] ->
        Reachable = Currents ;
        getReachable(Edges, NewCurrents, Reachable)).

% Iteracja BFS-a strefowego.
nextLayer([], _Currents, Acc, Acc).
nextLayer([fp(To, _, From) | TEdges], Currents, Acc, NextLayer) :-
    member(From, Currents), \+ member(To, Currents), \+ member(To, Acc),
    !, % Ten wykrzyknij jest czerwony, ale żeby był zielony
       %   drugą klazule by trzeba napisać trzykrotnie
    nextLayer(TEdges, Currents, [To | Acc], NextLayer).
nextLayer([_ | TEdges], Currents, Acc, NextLayer) :-
    nextLayer(TEdges, Currents, Acc, NextLayer).

% Tworzy zbalansonawane drzewo BST na podstawie posortowanej listy.
constructBST([], leaf).
constructBST(List, Tree) :-
    (divList(List, Left, Right) -> true ; divListOdd(List, Left, Right)),
    Right = [Val | TRight],
    constructBST(Left, LeftTree),
    constructBST(TRight, RightTree),
    Tree = node(Val, LeftTree, RightTree).

% Dzieli listę na pół (o parzystej długości).
divList(L, Left, Right) :-
    append(Left, Right, L),
    length(Left, N),
    length(Right, N).

% Dzieli listę na pół (o nieparzystej długości).
divListOdd(L, Left, Right) :-
    reverse(L, [H | LV]),
    reverse(LV, LR),
    divList(LR, Left, T),
    append(T, [H], Right).

% Sprawdza czy element jest w drzewie.
memberBST(Elem, node(Elem, _, _)).
memberBST(Elem, node(Val, _LeftTree, RightTree)) :-
    Elem @> Val, memberBST(Elem, RightTree).
memberBST(Elem, node(Val, LeftTree, _RightTree)) :-
    Elem @< Val, memberBST(Elem, LeftTree).

% empty(+Automat)
% Odnosi sukces wtw, gdy język akceptowany przez podany automat jest pusty.
% Dzięki zastosowaniu zrównażonych drzew BST odpowiedź jest udzielana w O(logn).
empty(AutomatRaw) :-
    correct(AutomatRaw, Automat),
    automatum(_, _, _, Start, _, Reachable) = Automat,
    \+ memberBST(Start, Reachable).

% Struktura listy róznicowej.
:- op(500, xfy, '--').
% Dodanie elementu.
insert(Elem, Front -- Q, Front -- QN) :- Q = [Elem | QN].
% Pobranie elementu
take(Front -- Q, NewFront -- Q, Elem) :- Front = [Elem | NewFront].
% Sprawdzenie czy kolejka jest pusta
isEmpty(Front -- _Q) :- var(Front).

% accept(+Automat, ?Słowo)
% Odnosi sukces wtw, gdy podany Automat akceptuje słowo Słowo.
accept(AutomatRaw, Word) :-
    correct(AutomatRaw, Automat),
    automatum(_, _, _, Start, _, _) = Automat,
    First = (Start, []),
    Queue = [First | X] -- X,
    bfs(Automat, Queue, Word).

% Tworzenie kolejnych słów przeszukiwaniem wszerz.
bfs(automatum(_, _, _, _, Ends, _), Queue, Result) :-
    \+ isEmpty(Queue),
    take(Queue, _, (Current, Word)),
    memberBST(Current, Ends),
    reverse(Word, Result). % Kolejne litery były dodawane na początek listy.

% Dzięki zastosowaniu tablicy róznicowej, operacja dorzucenia elementu na
%   koniec kolejki odbywa się w czasie stałym, a nie liniowym
%   jak miałoby to miejsce przy standardowej liście.
bfs(automatum(Alphabet, Vertices, Edges, Start, Ends, Reachable), Queue, Result) :-
    \+ isEmpty(Queue),
    take(Queue, TQueue, (Current, Word)),
     % Guarding dla tablic skończonych.
    (var(Result) -> true ; length(Result, LR), length(Word, LW), LW =< LR),

    getNeighbours(Current, Reachable, Edges, NextEdges),
    pushWords(Word, NextEdges, NextCalls),
    insertList(NextCalls, TQueue, NewQueue),
    bfs(automatum(Alphabet, Vertices, Edges, Start, Ends, Reachable), NewQueue, Result).

% Dodanie wszystkich elementów do listy
insertList([], DL, DL).
insertList([H | T], DL, NL) :- insert(H, L, NL), insertList(T, DL, L).

% Pobranie sąsiadów danego wierzchołka
getNeighbours(_Current, _Reachable, [], []).
getNeighbours(Current, Reachable,
    [fp(Current, C, Next) | TEdges], [fp(Current, C, Next) | TResult]) :-
    memberBST(Next, Reachable), % Odrzucenie wejscia w ścieżki bez wyjścia.
    !, % Odciecie żeby nie rozpisywać kolejnej klauzuli na cztery inne.
    getNeighbours(Current, Reachable, TEdges, TResult).
getNeighbours(Current, Reachable, [ _ | TEdges], TResult) :-
    getNeighbours(Current, Reachable, TEdges, TResult).

% Budowa słowa - dodanie liter z krawędzi.
pushWords(_, [], []).
pushWords(Word, [fp(_, C, To) | TNextEdges], [(To, [C | Word]) | TNextCalls]) :-
    pushWords(Word, TNextEdges, TNextCalls).

% equal(+Automat1, +Automat2)
% Odnosi sukces wtw, gdy L(Automat1) = L(Automat2) oraz alfabety obu automatów są równe.
equal(AutomatRaw1, AutomatRaw2) :-
    correct(AutomatRaw1, Automat1), correct(AutomatRaw2, Automat2),
    automatum(Alphabet1, Vertices1, Edges1, Start1, Ends1, _) = Automat1,
    automatum(Alphabet2, Vertices2, Edges2, Start2, Ends2, _) = Automat2,
    Alphabet1 == Alphabet2,
    complementSet(Vertices1, Ends1, InvEnds1),
    complementSet(Vertices2, Ends2, InvEnds2),

    sort(InvEnds1, InvEndsSorted1),
    sort(InvEnds2, InvEndsSorted2),
    constructBST(InvEndsSorted1, InvEnds1Tree),
    constructBST(InvEndsSorted2, InvEnds2Tree),

    \+ findWayIntersect(Automat1,
        automatum(Alphabet2, Vertices2, Edges2, Start2, InvEnds2Tree, _),
        [(Start1, Start2)], []),
    \+ findWayIntersect(Automat2,
        automatum(Alphabet1, Vertices1, Edges1, Start1, InvEnds1Tree, _),
        [(Start1, Start2)], []).

% subsetEq(+Automat1, +Automat2)
% Odnosi sukces wtw, gdy L(Automat1) ⊆ L(Automat2) oraz alfabety obu automatów są równe.
subsetEq(AutomatRaw1, AutomatRaw2) :-
    correct(AutomatRaw1, Automat1), correct(AutomatRaw2, Automat2),
    automatum(Alphabet1, _, _, Start1, _, _) = Automat1,
    automatum(Alphabet2, Vertices2, Edges2, Start2, Ends2, _) = Automat2,
    Alphabet1 == Alphabet2,
    complementSet(Vertices2, Ends2, InvEnds2),
    sort(InvEnds2, InvEndsSorted2),
    constructBST(InvEndsSorted2, InvEnds2Tree),

    \+ findWayIntersect(Automat1,
        automatum(Alphabet2, Vertices2, Edges2, Start2, InvEnds2Tree, _),
        [(Start1, Start2)],[(Start1, Start2)]).

% Wykonuje dopełnienie zbioru stanów akceptujących -> tworzy automat dopełnienia języka.
complementSet([], _Ends, []).
complementSet([V | TVertices], Ends, [V | Complement]) :-
    \+ memberBST(V, Ends), complementSet(TVertices, Ends, Complement).
complementSet([V | TVertices], Ends, Complement) :-
    memberBST(V, Ends), complementSet(TVertices, Ends, Complement).

% Znajduje ścieżke od startu do stanu akceptującego w iloczynie automatów.
findWayIntersect(automatum(_, _, _, _, Ends1, _),
    automatum(_, _, _, _, Ends2, _), [(Current1, Current2) | _], _) :-
    memberBST(Current1, Ends1),
    memberBST(Current2, Ends2),
    !. % Znalezienie odpowiedzi i przerwanie dalszego wykonywania.

findWayIntersect(automatum(Alphabet1, Vertices1, Edges1, Start1, Ends1, _),
    automatum(Alphabet2, Vertices2, Edges2, Start2, Ends2, _),
    [(Current1, Current2) | TQueue], Visited) :-
    % Parowanie przejscia dla obu automatów po tej samej literze.
    getEdge(fp(Current1, C, Destination1), Edges1),
    getEdge(fp(Current2, C, Destination2), Edges2),
    % Sprawdzenie czy dany stan już nie był odwiedzony.
    \+ member((Destination1, Destination2), Visited),
    findWayIntersect(
        automatum(Alphabet1, Vertices1, Edges1, Start1, Ends1, _),
        automatum(Alphabet2, Vertices2, Edges2, Start2, Ends2, _),
        [(Destination1, Destination2) | TQueue], [(Destination1, Destination2) | Visited]).

% Filtrowania po zbiorze krawędzi.
getEdge(fp(From, On, To), [fp(From, On, To)| _TEdges]).
getEdge(X, [_ | TEdges]) :- getEdge(X, TEdges).

%%%%%%% TESTS %%%%%%%
example(a11, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1)], 1, [2,1])).
example(a12, dfa([fp(x,a,y),fp(x,b,x),fp(y,a,x),fp(y,b,x)], x, [x,y])).
example(a2, dfa([fp(1,a,2),fp(2,b,1),fp(1,b,3),fp(2,a,3),fp(3,b,3),fp(3,a,3)], 1, [1])).
example(a3, dfa([fp(0,a,1),fp(1,a,0)], 0, [0])).
example(a4, dfa([fp(x,a,y),fp(y,a,z),fp(z,a,x)], x, [x])).
example(a5, dfa([fp(x,a,y),fp(y,a,z),fp(z,a,zz),fp(zz,a,x)], x, [x])).
example(a6, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1)], 1, [])).
example(a7, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1),fp(3,b,3),fp(3,a,3)], 1, [3])).

example(b1, dfa([fp(1,a,1),fp(1,a,1)], 1, [])).
example(b2, dfa([fp(1,a,1),fp(1,a,2)], 1, [])).
example(b3, dfa([fp(1,a,2)], 1, [])).
example(b4, dfa([fp(1,a,1)], 2, [])).
example(b5, dfa([fp(1,a,1)], 1, [1,2])).
example(b6, dfa([], [], [])).

example(b10, dfa([fp(1,a,1), fp(1,b,1)], 5, [1])).
example(b11, dfa([fp(1,a,1), fp(1,b,1)], 1, [5])).

example(a0, dfa([fp(1,a,1), fp(1,b,1)], 1, [1])).
example(d1, dfa([fp(1,a,3), fp(1, b, 2), fp(2, b, 3), fp(2, a, 4), fp(3, a, 4), fp(3, b, 5), fp(4, a, 5), fp(4, b, 5), fp(5, a, 5), fp(5, b, 5)], 1, [2,3,4])).
example(d2, dfa([fp(1,a,3), fp(1, b, 2), fp(2, b, 3), fp(2, a, 4), fp(3, a, 4), fp(3, b, 5), fp(4, a, 5), fp(4, b, 5),
    fp(5, a, 6), fp(5, b, 6), fp(6, a, 7), fp(6, b, 7), fp(7, a, 5), fp(7, b, 5)], 1, [2,3,4])).

example(w1, dfa([fp(1,a,2), fp(1,b,2), fp(2,a,2), fp(2,b,2)], 1, [2])).
example(w2, dfa([fp(1,a,1), fp(1,b,1)], 1, [1])).

test :- example(a11, X), write(X), write("\n"), correct(X, Y), write(Y).
test2 :- example(a6, A), write(A), write("\n"), empty(A).
test2a :- example(a2, A), write(A), write("\n"), empty(A).
test3 :- example(a6, X), correct(X, Y), automatum(_, _, E, _, _, _, _) = Y, getEdge(S, E), write(S).
test4 :- getReachable([fp(1,a,2),fp(2,b,1),fp(1,b,3),fp(3,b,3)], [1], R), write(R).
test5 :- example(a11, A), correct(A, R), accept(A, V), write(R), write("\n"), write(V), write("\n").
test6 :- example(a2, A), example(a11, B), subsetEq(A, B).
testQQ :- example(b10, A), example(b11,B),  \+ correct(A, _), \+ correct(B, _), write("Passed!").


% Packs
testUlt :-
    example(a6, C), empty(C),
    example(a7, B), empty(B),
    example(a2, A), accept(A, []),
    example(a2, A), accept(A, [a,b]),
    example(a2, A), accept(A, [a,b,a,b]),

    example(a11, A1), example(a12, B1), equal(A1, B1),
    example(a2, A2), example(a11, B2), subsetEq(A2, B2),
    example(a5, A3), example(a3, B3), subsetEq(A3, B3).

testUlt2 :-
    example(b1, A5), \+ correct(A5, _),
    example(a2, A6), \+ empty(A6),
    example(a3, A7), example(a4, B7), \+ equal(A7, B7),
    example(a4, A8), example(a3, B8), \+ subsetEq(A8, B8),
    example(a2, A9), \+ accept(A9, [a]).


% WORKING (true)
% example(a6, A), empty(A).
% example(a7, A), empty(A).

% example(a2, A), accept(A, [])
% example(a2, A), accept(A, [a,b])
% example(a2, A), accept(A, [a,b,a,b])

% example(a11, A), accept(A, [X,Y,Z])
% example(a11, A), accept(A, Var).

% example(a11, A), example(a12, B), equal(A, B).
% example(a2, A), example(a11, B), subsetEq(A, B).
% example(a5, A), example(a3, B), subsetEq(A, B).


% Working (false)
% example(b1, A), correct(A, _). % b2, b3, b4, b5 - też porażki
% example(a2, A), empty(A).
% example(a3, A), example(a4, B), equal(A, B).
% example(a4, A), example(a3, B), subsetEq(A, B).
% example(a2, A), accept(A, [a]).
