newPackage(
    "Chambers",
    Version => "0.9",
    Date => "April 19, 2022",
    Authors => {
	{Name => "Lauren Cranton Heller", Email => "lch@math.berkeley.edu"},
	{Name => "Mahrud Sayrafi",        Email => "mahrud@math.umn.edu"}
	},
    Headline => "construct sheaves on toric varieties from maximal chambers",
    PackageImports => {"Polyhedra", "Truncations"},
    PackageExports => {"NormalToricVarieties", "LinearTruncations", "SimplicialComplexes"},
    DebuggingMode => true
    )

export{
    "primitiveCollections",
    "primitiveRelation",
    "chambersFromRelation",
    "idealFromChamber",
    "movGenerators",
    "secondaryFan",
    "chambers",
    "adjacentChambers",
    "fanFromIdeal",
    "conesFromIdeal",
    "degreeMap",
    "ringMap",
    "mapPresentation"
    }

-- TODO: use this more
exportFrom_Truncations {"effGenerators"}

-- TODO: replace the one in Core
nonempty = x -> select(x, i -> #i > 0)

-- move elements of L according to w
move = (w, L) -> apply(L, i -> position(w, j -> i == j))

-------------------------

-- finds all primitive collections of a toric variety
primitiveCollections = method()
primitiveCollections NormalToricVariety := X -> (
    isInCone := I -> any(X.max, C -> isSubset(I, C));
    -- TODO: this can get very slow
    select(subsets length rays X, I ->
	not isInCone I and all(subsets(I, #I - 1), isInCone))
    )

-- calculates the primitive relation associated to a collection
primitiveRelation = method()
primitiveRelation(NormalToricVariety, List) := memoize((X, I) -> (
    -- FIXME: use the effGenerators matrix
    s := transpose matrix { sum (rays X)_I };
    F := fan X;
    m := rays F;
    C := first flatten apply(dim F + 1,
	d -> select(cones(d, F), c -> inInterior(s, coneFromVData m_c)));
    r := solve(m_C, s);
    h1 := hashTable apply(I, i -> vector (rays X)_i => 1);
    h2 := hashTable apply(#C, i -> m_(C_i) => - r_(i,0));
    -- TODO: clear denominators
    merge(h1, h2, plus)
    ))
-- TODO: cache properly

-------------------------

-- identifies the chamber separated from the Nef cone
-- from the facet associated to a primitive relation
chambersFromRelation = method()
chambersFromRelation(NormalToricVariety, HashTable) := Matrix => (X, r) -> (
    vecs := transpose matrix rays X;
    coef := apply(#rays X,
	a -> if r#?(vecs_a) then r#(vecs_a) else 0);
    A := transpose matrix {coef};
    degs := matrix degrees ring X;
    s := numcols degs;
--    wall := coneFromVData gens ker 
    A = transpose(degs \\ A);
--    cham := coneFromVData \ chambers X;
    nefc := coneFromVData nefGenerators X;
    select(adjacentChambers(X,nefc),
	wall -> numcols wall == s-1 and A*wall == 0)
    )

-- calculates the irrelevant ideal corresponding to fixing a chamber as the Nef cone
-- TODO: also do chamberFromIdeal
idealFromChamber = method()
idealFromChamber(NormalToricVariety, Matrix) :=
idealFromChamber(NormalToricVariety, Cone)   := Ideal => (X, C) -> idealFromChamber(ring X, C)
idealFromChamber(Ring,               Matrix) := Ideal => (S, N) -> idealFromChamber(S, coneFromVData N)
idealFromChamber(Ring,               Cone)   := Ideal => (S, C) -> (
    mons := select(nonempty subsets gens S,
	-- TODO: change to only look at subsets of size the Picard rank of X
	-- TODO: contains acts funny with cones of different dimension
	ell -> contains(coneFromVData transpose matrix(degree \ ell), C));
    trim ideal(product \ mons)
    )

-- find the generators of the moving cone
movGenerators = method(TypicalValue => Matrix)
movGenerators Ring :=
movGenerators NormalToricVariety := X -> movGenerators cover(QQ ** effGenerators X)
movGenerators Matrix := A -> (
    rays intersection apply(numcols A,
	i -> coneFromVData submatrix'(A, , {i})))

-- find the secondary fan
secondaryFan = method(TypicalValue => Fan)
secondaryFan NormalToricVariety := X -> secondaryFan cover(QQ ** effGenerators X)
secondaryFan Matrix := lookup(ccRefinement, Matrix)

maxMatrices := F -> ( A := rays F; apply(maxCones F, sigma -> A_sigma) )

-- finds all maximal chambers in Eff
chambers = method(TypicalValue => List)
chambers NormalToricVariety := X -> chambers cover(QQ ** effGenerators X)
chambers Matrix := (cacheValue symbol chambers) (m -> maxMatrices secondaryFan m)

-*
-- FIXME: not currently working, but potentially much faster
needsPackage "gfanInterface"
gcd Matrix := m -> gcd flatten entries m
X = fano(2, 3) -- (2, 4)
F = gfanSecondaryFan rays X
B = concatCols apply(cols rays F, ell -> first fourierMotzkin(ell, linSpace F))
B = rays F
p = transpose gens ker transpose linSpace F
A = concatCols apply(cols(p * B), c -> c // gcd c); A_(sortColumns A)
A = rays fan chambers X; A_(sortColumns A)
*-

--
adjacentChambers = method()
adjacentChambers(NormalToricVariety, Cone) := (X, C) -> (
    cham := coneFromVData \ chambers X;
    adja := select(cham, D -> commonFace(C,D));
    full := new HashTable from apply(adja, D -> (
	    CD := intersection(C,D);
	    rays D => rays CD
	    ));
    wall := new HashTable from apply(rays \ facesAsCones(1,C),
	D -> D => D);
    merge(full, wall, identity)
    )

-*
chambers NormalToricVariety := X -> (
    degs := matrix degrees ring X;
    wall := subsets(numrows degs, numcols degs - 1);
    hyps := apply(wall, ell -> transpose gens ker degs^ell);
    l := #wall;
    sign := apply(2^l, a -> apply(l, b -> (
		ret := a % 2^(b+1);
		a = a - ret;
		(-1)^(ret/(2^b))
		)));
    cons := apply(sign,
	ell -> fold((A,B) -> A || B, apply(l, i -> (ell_i)*hyps_i)));
    E := coneFromVData transpose degs;
    unique(rays \ select(coneFromHData \ cons,
	    C -> (dim C == rank source degs) and contains(E, C))))
*-

conesFromIdeal = B -> (
    if numgens B == 0 then error "expected nonzero irrelevant ideal";
    apply(flatten(exponents \ B_*),
	ell -> positions(ell, i -> i == 0))
    )

-- TODO: this description is wrong
-- returns the toric variety, list of variables, and degree map
-- given by changing the irrelevant ideal
fanFromIdeal = method()
fanFromIdeal(NormalToricVariety, Ideal) := (X,    B) -> fanFromIdeal(ring X, rays X, B)
fanFromIdeal(Ring, List,         Ideal) := (S, A, B) -> (
    maxs := conesFromIdeal trim B;
--    used := sort unique flatten maxs;
--    maxs  = move_used \ maxs;
    -- FIXME: this line makes fanFromIdeal SIGNIFICANTLY slower than just conesFromIdeal
    --fan apply(maxs, ell -> coneFromVData transpose matrix A_ell)
    -- this is silly and is also slow, but not as much
    -- FIXME: fan sometimes reorders the rays
    fan normalToricVariety(A, maxs)
    )

selectPositions = method()
selectPositions(List,List) := (M, L) -> (
    apply(M, m -> (
	    posi := positions(L, l -> l == m);
	    if #posi == 0 then error "not sublist";
	    if #posi >  1 then error "repeated entries";
	    posi_0
    	    ))
    )
-- TODO: make this faster / do something better

degreeMap = method()
degreeMap(NormalToricVariety, NormalToricVariety) := (Y, X) -> (
    (degs1, degs2) := (degrees ring X, degrees ring Y);
    -- TODO: implement for degenerate varieties?
    used := selectPositions(rays Y, rays X);
    zeros := toList(rank picardGroup Y : 0);
    C := new MutableList from (numgens ring X : zeros);
    scan(#used, a -> C#(used_a) = degs2_a);
    C  = matrix toList C;
    (used, transpose(C // matrix degs1))
    )

ringMap = method()
ringMap(NormalToricVariety, NormalToricVariety) := (Y,X) -> (
    (S, R) := (ring X, ring Y);
    (degs1, degs2) := (degrees R, degrees S);
    -- TODO: implement for degenerate varieties?
    used := selectPositions(rays Y, rays X);
    H := new HashTable from apply(#used, a -> used_a => a);
    f := apply(numgens S, a -> if H#?a then R_(H#a) else 1_R);
    map(R, S, f)
    )
-- TODO: cache

-- TODO: should this return the new irrelevant ideal also?
selectVariables(List, PolynomialRing, Matrix) := (L, S, A) -> (
    L = sort L;
    -- TODO: allow vars in different order
    deg := A * effGenerators S;
    T := newRing(S, Degrees => entries transpose deg);
    F := map(T, S);
    R := first selectVariables(L, T);
    H := new HashTable from apply(#L, a -> L_a => a);
    f := apply(numgens S, a -> if H#?a then R_(H#a) else 1_R);
--  f := new MutableList from (numgens S : 1);
--  scan(#L, a -> f#(L_a) = R_a);
    G := map(R, T, f);
    (R, G * F)
    )

mapPresentation = method()
mapPresentation(RingMap, Module, Matrix) := (f, M, A) -> (
    R := target f;
    if M == 0 then return module ideal 0_R;
    pres := matrix apply(entries presentation M, ell -> f \ ell);
    degs := entries((matrix degrees M)*(transpose A));
    if pres == 0 then R^(-degs) else cokernel map(R^(-degs), , pres)
    )
mapPresentation(NormalToricVariety, NormalToricVariety, Module) := (Y, X, M) -> (
    f := ringMap(Y, X);
    A := last degreeMap(Y, X);
    mapPresentation(f, M, A)
    )

-------------------------

-*
topSyzygies = method()
topSyzygies(NormalToricVariety) := X -> (
    F := facesAsCones(1,coneFromVData nefGenerators X);
    apply(F, C -> (
	    d := first entries transpose interiorVector C;
	    M := first entries basis(d,S);
	    lcm M
    )
*-

-------------------------

beginDocumentation()

TEST ///
  -- check idealFromChamber for all five smooth Fano toric varieties
  scan(5, i -> assert(
	  ideal(X := smoothFanoToricVariety(2, i)) ==
	  idealFromChamber(ring X, nefGenerators X)))
///

-------------------------

doc ///
Key
  Chambers
Headline
  changing the irrelevant ideal of a toric variety
Description
  Text
    Let X be a normal toric variety.
///

end--

restart
needsPackage "Chambers"
X = smoothFanoToricVariety(2, 3)
X = hirzebruchSurface 3
S = ring X

P = primitiveCollections X
R = primitiveRelation_X \ P
CX = chambers X
rays X
degrees ring X
C = chambersFromRelation_X \ R

idealFromChamber(X, CX_1) == ideal X
decompose idealFromChamber(X, CX_0) 
F0 = fanFromIdeal(X, idealFromChamber(X, CX_0) )
rays normalToricVariety F0
isWellDefined oo
Bs = (ell -> idealFromChamber_X \ ell) \ keys \ C

F = fanFromIdeal(X,Bs_0_0)
Y = normalToricVariety F
(K,A) = degreeMap(Y,X)
(R,f) = selectVariables(K,S,A)

res prune M
res prune (f**M)

describe Y
isWellDefined Y

sum Bs + ideal X
I = trim oo
decompose I
netList supportOfTor res I

apply(R, r -> apply(#rays X, a -> if r#?(vecs_a) then r#(vecs_a) else 0))

--
restart
needsPackage "Chambers"


crossTheWall = method()
-- given 
crossTheWall(NormalToricVariety, List) := (X, I) -> (
    R := primitiveRelation(X, I);
    C := chambersFromRelation(X, R);
    B := idealFromChamber(X, C);
    )

output=for j from 1 to 5 list (
L=apply(random(1,3),i->apply(2,j->random(-4,-1)));
print L;
mins=apply(2,i->min(apply(L,ell->ell_i)));
N=apply(random(1,5),i->apply(2,j->random(mins_j,0)));
print N;
M = cokernel random(S^N,S^L);
print toExternalString M;
print res prune M; print res prune mapPresentation(Y,X,M);
M
);

nef = coneFromVData nefGenerators X
eff = coneFromVData effGenerators S


scan(12, i -> (
	d = {-i,i};
	print netList apply(supportOfTor truncate(d,M,symbol Cone => eff), ell -> apply(ell, c -> c-d));
	))

--
B =restart
needsPackage "Chambers"

needs "helpers.m2"
needs "truncate.m2"

-- scan(125, i -> print(i, movGenerators fano(4,i) != nefGenerators fano(4,i)))

X = fano(4, 8) -- and fano(4,15), and more?
X = hirzebruchSurface 3
S = ring X
L = chambers X
B = idealFromChamber(X, L#0)
X' = normalToricVariety(rays X, conesFromIdeal trim B, WeilToClass => effGenerators X)
-- FIXME: this sometimes reorders the rays, and hence the variables
--F' = fanFromIdeal(S, rays X, B)
--X' = normalToricVariety(F', WeilToClass => effGenerators X)
assert(effGenerators X' * matrix rays X' == 0)
S' = ring X
assert not isFano X' -- cool!
netList{decompose ideal X, decompose ideal X'}

(C0, C1) = (coneFromVData L#0, coneFromVData L#1)

mahrud({-3,-3}, {3,3}, (i,j) -> # unique degrees truncate({i,j}, S', symbol Cone => C0))
mahrud({-3,-3}, {3,3}, (i,j) -> # unique degrees truncate({i,j}, S,  symbol Cone => C1))

rays C1
movGenerators X
effGenerators X
chambers X
d = {1, 1}; netList supportOfTor res(S^{d}  ** module truncate(d, S,  symbol Cone => C1))
d = {-1, 3}; netList supportOfTor res(S'^{d} ** module truncate(d, S', symbol Cone => C0))

---
netList apply(L, chamb -> (
	C := coneFromVData chamb;
	d := 2 * first vecs interiorVector C;
	supportOfTor res(S^{d} ** module truncate(d, S, symbol Cone => C))
	))

--saturating truncation in different chambers
X = kleinschmidt(3,{2,3})
isWellDefined X
isFano X

S = ring X
B = ideal X
maxMatrices secondaryFan X

I = trunc(d,S);
tally degrees image mingens I
J = saturate(I,B)
