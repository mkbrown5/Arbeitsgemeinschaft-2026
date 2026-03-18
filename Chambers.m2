newPackage(
    "Chambers",
    Version => "0.92",
    Date => "March 14, 2026",
    Authors => {
	{Name => "Lauren Cranton Heller", Email => "lch@math.berkeley.edu"},
	{Name => "Mahrud Sayrafi",        Email => "mahrud@math.umn.edu"}
	},
    Headline => "construct sheaves on toric varieties from maximal chambers",
    PackageImports => {"Polyhedra", "Truncations"},
    PackageExports => {"NormalToricVarieties", "Topcom", "Graphs"},
    DebuggingMode => true
    )

export{
    "primitiveCollections",
    "primitiveRelation",
    "chambersFromRelation", -- TODO: find better name?
    "chamberFromIdeal",
    -- "conesFromIdeal", -- TODO
    "conesFromChamber",
    "idealFromChamber",
    -- "idealFromCones", -- TODO
    "movGenerators",
    "secondaryFan",
    "chambers",
    "secondaryFanWalls",
    "chamberGraph",
    "adjacentChambers",
    "conesFromIdeal",
    --
    "Bl2PP",
    --
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

-- TODO: is this the best way?
gale = m -> gens ker (if coker m == 0 then identity else transpose) m
-- TODO: can we use this? galeDualMatrix := matrix (fromWDivToCl X)^torsionlessCoord;

--------------------------------------------------------------------------------
-- REMOVE ME: starting M2 v1.26.05, toricBlowup accepts an option
--------------------------------------------------------------------------------

debug NormalToricVarieties
toricBlowup' = method(Options => { WeilToClass => null })
toricBlowup'(List, NormalToricVariety)       := NormalToricVariety => opts -> (s, X) -> (
    toricBlowup'(s, X, makePrimitive sum ((rays X)_s), opts))
toricBlowup'(List, NormalToricVariety, List) := NormalToricVariety => opts -> (s, X, v) -> (
    coneList := max X;
    starIndex := positions (coneList, t -> all (s, i -> member (i,t)));
    star := coneList_starIndex;
    rayMatrix := transpose matrix rays X;
    d := dim X;
    clStar := {};
    if member(sort s, coneList)
    then clStar = subsets(sort s, d-1)
    else for t in star do (
    	c := 1 + d - rank rayMatrix_t;
    	clStar = clStar | select (orbits(X,c), r -> all (r, j -> member(j,t)))
	);
    clStar = unique clStar;
    n := #rays X;
    coneList = coneList_(select (#coneList, i -> not member (i, starIndex)));
    if #s === 1 then (
    	coneList' := for t in clStar list (
      	    if member (s#0,t) then continue
      	    else sort (t | s)
	    );
	Z := normalToricVariety(rays X, coneList | coneList',
	    CoefficientRing => X.cache.CoefficientRing,
	    Variable        => X.cache.Variable,
	    WeilToClass     => opts.WeilToClass);
        Z.cache.toricBlowup' = X;
        return Z
	);
    coneList' = for t in clStar list (
	if all (s, i -> member (i,t)) then continue
	else t | {n}
	);
    Z = normalToricVariety(rays X | {v}, coneList | coneList',
	CoefficientRing => X.cache.CoefficientRing,
	Variable        => X.cache.Variable,
	WeilToClass     => opts.WeilToClass);
    Z.cache.toricBlowup' = X;
    Z
    );

--------------------------------------------------------------------------------
-- Primitive collections and wall relations
--------------------------------------------------------------------------------
-- These routines extract the combinatorial data that controls wall crossings
-- in the secondary fan of a simplicial normal toric variety.

-- Will be soon moved to NormalToricVarieties
-- finds all primitive collections of a toric variety
primitiveCollections = method()
primitiveCollections NormalToricVariety := X -> (
    isInCone := I -> any(X.max, C -> isSubset(I, C));
    -- TODO: this can get very slow
    select(subsets length rays X,
	I -> not isInCone I and all(subsets(I, #I - 1), isInCone))
    )
-- TODO: is this correct?
primitiveCollections NormalToricVariety := X -> indices \ (dual monomialIdeal X)_*

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

chambersFromRelation = method()
chambersFromRelation(NormalToricVariety, HashTable) := Matrix => (X, r) -> (
    -- identifies the chamber separated from the nef cone
    -- from the facet associated to a primitive relation
    vecs := transpose matrix rays X;
    coef := apply(#rays X,
	a -> if r#?(vecs_a) then r#(vecs_a) else 0);
    A := transpose matrix {coef};
    degs := matrix degrees ring X;
    s := numcols degs;
--    wall := coneFromVData gens ker
    A = transpose(A // degs);
--    cham := coneFromVData \ chambers X;
    nefc := coneFromVData nefGenerators X;
    select(adjacentChambers(X,nefc),
	wall -> numcols wall == s-1 and A*wall == 0)
    )

--------------------------------------------------------------------------------
-- Conversion tools for different representations of a chamber
-- e.g. the nef cone of X, maximal cones of X, the irrelevant ideal, etc.
--------------------------------------------------------------------------------

conesFromChamber = method()
conesFromChamber(List, Matrix, Matrix) := List => (L, eff, nef) -> conesFromChamber(L, eff, coneFromVData nef)
conesFromChamber(List, Matrix, Cone)   := List => (L, eff, nef) -> (
    -- returns the list of maximal cones corresponding to:
    -- L: the list of rays
    -- eff: the degree matrix
    -- nef: a chamber in the secondary fan
    d := length L - ambDim nef;
    a := solve(eff, interiorVector nef);
    sort select(nonempty subsets(#L),
	ell -> (
	    -- TODO: double check this!!
	    m := solve(matrix L_ell, -a^ell);
	    v := entries(matrix L * m + a);
	    ell' := toList(0..#L-1) - set ell;
	    all(ell, i -> v#i == {0}) and
	    all(ell', i -> v#i > {0}))
	)
    )

-- TODO: chamberFromCones

conesFromIdeal = method()
conesFromIdeal Ideal := List => B -> (
    if numgens B == 0 then error "expected nonzero irrelevant ideal";
    -- variables _not_ present in a generator of B span the corresponding maximal cone
    apply(flatten(exponents \ B_*),
	ell -> positions(ell, i -> i == 0))
    )

-- TODO: idealFromCones

idealFromChamber = method()
idealFromChamber(NormalToricVariety, Matrix) :=
idealFromChamber(NormalToricVariety, Cone)   := Ideal => (X, nef) -> idealFromChamber(ring X, nef)
idealFromChamber(PolynomialRing,     Matrix) := Ideal => (S, nef) -> idealFromChamber(S, coneFromVData nef)
idealFromChamber(PolynomialRing,     Cone)   := Ideal => (S, nef) -> (
    -- the irrelevant ideal corresponding to fixing a chamber as the nef cone
    eff := effGenerators S;
    sigmas := conesFromChamber(entries gale eff, eff, nef);
    ideal apply(sigmas, sigma -> product(S_* - set S_*_sigma))
    -- mons := select(nonempty subsets gens S,
    -- 	ell -> contains(coneFromVData transpose matrix(degree \ ell), nef));
    -- trim ideal(product \ mons)
    )

chamberFromIdeal = method()
chamberFromIdeal Ideal := Cone => B -> (
    -- find the chamber in the secondary fan
    -- corresponding to an irrelevant ideal
    eff := effGenerators ring B;
    rays intersect apply(indices \ B_*,
	ell -> coneFromVData eff_ell))

--------------------------------------------------------------------------------
-- New NormalToricVariety constructors for a given chamber
--------------------------------------------------------------------------------

normalToricVariety(NormalToricVariety, Matrix) :=
normalToricVariety(NormalToricVariety, Cone)   := opts -> (X, nef') -> (
    -- the birational toric variety corresponding to the given nef cone
    normalToricVariety(rays X, effGenerators X, nef', opts))
normalToricVariety(NormalToricVariety, Ideal)  := opts -> (X, B') -> (
    -- the birational variety corresponding to the given irrelevant ideal
    if B' == ideal X then X else
    normalToricVariety(rays X, conesFromIdeal trim B', opts,
	WeilToClass => effGenerators ring B'))

normalToricVariety(List, Matrix, Matrix) :=
normalToricVariety(List, Matrix, Cone)   := opts -> (rayList, eff, nef) -> (
    -- the toric variety corresponding to the given rays and nef cone
    normalToricVariety(rayList, conesFromChamber(rayList, eff, nef), opts, WeilToClass => eff))

normalToricVariety(List, PolynomialRing, Matrix) :=
normalToricVariety(List, PolynomialRing, Cone)   := opts -> (rayList, S, nef) -> (
    -- the toric variety corresponding to the given rays, Cox ring, and nef cone
    normalToricVariety(rayList, effGenerators S, nef, opts))
normalToricVariety(List, Ideal) := opts -> (rayList, B) -> (
    -- the toric variety corresponding to the given rays and irrelevant ideal
    normalToricVariety(rayList, conesFromIdeal trim B, opts,
	WeilToClass => effGenerators ring B))

--------------------------------------------------------------------------------
-- The secondaryFan, moving cone, and chambers
--------------------------------------------------------------------------------

-- find the generators of the moving cone
movGenerators = method(TypicalValue => Matrix)
movGenerators PolynomialRing :=
-- TODO: see below
movGenerators NormalToricVariety := X -> movGenerators cover(QQ ** effGenerators X)
movGenerators Matrix := eff -> (
    -- TODO: should this use ZZ-module intersection instead?
    rays intersection apply(numcols eff,
	i -> coneFromVData submatrix'(eff, , {i})))

-- find the secondary fan
secondaryFan = method(TypicalValue => Fan)
-- TODO: see above
secondaryFan Matrix  := m -> fan apply(chambers m, coneFromVData)
secondaryFan Variety := X -> secondaryFan cover(QQ ** effGenerators X)

-- also can get maxCones this way:
-- topcomAllTriangulations(matrix transpose rays X, Homogenize => false, Fine => false)
maxMatrices := F -> ( A := rays F; apply(maxCones F, sigma -> A_sigma) )

-- finds all maximal chambers in Eff
chambers = method(TypicalValue => List)
-- TODO: should the chambers be in Pic(X) or Cl(X)?
chambers Variety := X -> X.cache.chambers ??= chambers cover(QQ ** effGenerators X)
chambers Matrix := m -> m.cache.chambers ??= (
    d := dim coneFromVData m;
    allFans := topcomAllTriangulations(m, Homogenize => false, Fine => true);
    allCones := new MutableHashTable from { m => true };
    cachedCones := new MutableHashTable;
    for F in allFans do (
	for C in keys allCones do (
	    remove(allCones, C);
	    C = coneFromVData C;
	    apply(F, sigma -> (
		    cachedCones#sigma ??= coneFromVData m_sigma;
		    C' := intersect(cachedCones#sigma, C);
		    if dim C' == d then allCones#(rays C') = true))));
    keys allCones)

--------------------------------------------------------------------------------
-- Helpers for wall crossing
--------------------------------------------------------------------------------

adjacentChambers = method()
adjacentChambers(NormalToricVariety, Matrix) := (X, C) -> adjacentChambers(X, coneFromVData C)
adjacentChambers(NormalToricVariety, Cone)   := (X, C) -> (
    -- keys are adjacent chambers or boundary walls,
    -- values are their common faces with C
    cham := coneFromVData \ chambers X;
    adja := select(cham, D -> commonFace(C,D));
    full := new HashTable from apply(adja, D -> (
	    CD := intersection(C,D);
	    rays D => rays CD
	    ));
    wall := new HashTable from apply(rays \ facesAsCones(1,C), D -> D => D);
    merge(full, wall, identity)
    )
-- adjacentChambers(Fan, Cone) := (F, C) -> (
--     A := rays F;
--     cham := apply(maxCones F, ell -> coneFromVData A_ell);
--     adja := select(cham, D -> commonFace(C, D));
--     full := hashTable apply(adja,
-- 	D -> rays D => rays intersection(C, D));
--     wall := hashTable apply(rays \ facesAsCones(1,C),
-- 	D -> D => D);
--     merge(full, wall, identity)
--     )

coneWalls = C -> rays \ facesAsCones(1, coneFromVData C)

secondaryFanWalls = method(TypicalValue => HashTable)
secondaryFanWalls Matrix := eff -> (
    -- keys:   walls (edges)
    -- values: chambers sharing a wall (vertices)
    cham := chambers eff;
    data := new MutableHashTable;
    for C in chambers eff do (
	for W in coneWalls C do (
	    if not data#?W then data#W = {C}
	    else data#W = append(data#W, C)));
    new HashTable from data)
secondaryFanWalls Variety := X -> X.cache.secondaryFanWalls ??= secondaryFanWalls cover(QQ ** effGenerators X)

-- TODO: should this have the toric varieties instead of chambers?
chamberGraph = method(TypicalValue => Graph)
chamberGraph Matrix := eff -> (
    -- keys:   chambers
    -- values: adjacent chambers
    cham := chambers eff;
    data := new MutableHashTable from apply(cham, C -> C => {});
    scan(values secondaryFanWalls eff,
	L -> if #L == 2 then (
	    (C, D) := (L#0, L#1);
	    data#C = unique append(data#C, D);
	    data#D = unique append(data#D, C)));
    graph data)
chamberGraph Variety := X -> X.cache.chamberGraph ??= chamberGraph cover(QQ ** effGenerators X)

selectPositions = method()
selectPositions(List, List) := (M, L) -> (
    apply(M, m -> (
	    posi := positions(L, l -> l == m);
	    if #posi == 0 then error "not sublist";
	    if #posi >  1 then error "repeated entries";
	    posi_0
	    ))
    )
-- TODO: make this faster / do something better

-- For Y obtained from a chamber of X, these routines construct the map
-- on divisor class groups, the induced Cox rings, and the transport
-- of a module presentation along that map.

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

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

Bl2PP = method(Options => { CoefficientRing => QQ , Variable => getSymbol "x" })
Bl2PP ZZ := NormalToricVariety => opts -> n -> (
    -- Bl_2(PP^n) with degrees based on Example 4.7 of arXiv:2501.00130
    PPn := toricProjectiveSpace(n, opts);
    Bl1 := toricBlowup'(toList(0..n-1), PPn, WeilToClass => matrix { toList(n+1:1) | {0},   toList(n:0) | {1,1}});
    X   := toricBlowup'(toList(1..n),   Bl1, WeilToClass => matrix { toList(n+1:1) | {0,0}, toList(n:0) | {1,1,0}, {1} | toList(n+1:0) | {1}});
    X)

--------------------------------------------------------------------------------
-- Documentation
--------------------------------------------------------------------------------

TEST ///
  -- check idealFromChamber for all five smooth Fano toric varieties
  scan(5, i -> assert(
	  ideal(X := smoothFanoToricVariety(2, i)) ==
	  idealFromChamber(ring X, nefGenerators X)))
///

TEST ///
  nonProjective = () ->(
      R := {
	  {0,0,1}, --v1
	  {4,0,1}, --v2
	  {0,4,1}, --v3
	  {1,1,1}, --v4
	  {2,1,1}, --v5
	  {1,2,1}, --v6
	  {-1,-1,-1} --v7
	  };
      Cpre := {
	  {1,3,6},{1,4,6},{1,2,4},{2,4,5},
	  {2,3,5},{3,5,6},{4,5,6},{1,3,7},
	  {1,2,7},{2,3,7}
	  };
      C := apply(Cpre, l-> l - {1,1,1});
      normalToricVariety(R, C)
      )
  X = nonProjective()
  --elapsedTime assert(53 == length chambers X) -- ~100s parallel, maybe 20min serial?
///

TEST ///
  assert(2 == length chambers hirzebruchSurface 4)
  assert(5 == length chambers smoothFanoToricVariety(2, 3))
  assert(4 == length chambers matrix {{1,1,1,1}, {1,1,-1,-1}, {1,-1,1,-1}})
///

TEST ///
  X0 = Bl2PP(5) -- with degrees based on Example 4.7 of arXiv:2501.00130
  S = ring X0
  A = rays X0
  eff = effGenerators X0
  nef = nefGenerators X0

  L = elapsedTime chambers X0
  C = apply(L, coneFromVData)
  B = apply(L, idealFromChamber_X0)
  M = apply(L, conesFromChamber_(A, eff))
  assert(B == apply(C, idealFromChamber_S))
  assert(L == apply(B, chamberFromIdeal))
  assert(M == apply(B, conesFromIdeal))
  assert(movGenerators X0 == matrix {{1, 1, 1, 1}, {0, 1, 0, 1}, {0, 0, 1, 1}})
  assert(secondaryFan X0 == fan C)

  assert(nefGenerators normalToricVariety(A,      B#0) == L#0)
  assert(nefGenerators normalToricVariety(A, S,   L#3) == L#3)
  assert(nefGenerators normalToricVariety(A, S,   C#4) == L#4)
  assert(nefGenerators normalToricVariety(A, eff, L#1) == L#1)
  assert(nefGenerators normalToricVariety(A, eff, C#2) == L#2)
  assert(nefGenerators normalToricVariety(X0,     L#2) == L#2)
  assert(nefGenerators normalToricVariety(X0,     B#1) == L#1)
  assert(nefGenerators normalToricVariety(X0,     C#0) == L#0)

  R = primitiveCollections X0
  assert(R == {{0, 1, 2, 3, 4}, {1, 2, 3, 4, 5}, {5, 6}, {0, 7}, {6, 7}})

  -- TODO: add assertions
  h = primitiveRelation(X0, first R) -- TODO: still too slow
  g = chambersFromRelation(X0, h) -- TODO: also too slow
  adjacentChambers(X0, nef)
  secondaryFanWalls X0
  chamberGraph X0
  -- degreeMap
  -- ringMap
  -- mapPresentation
///

--------------------------------------------------------------------------------
-- Documentation
--------------------------------------------------------------------------------

beginDocumentation()

doc ///
Node
  Key
    Chambers
  Headline
    computations in the secondary fan of a toric variety
  Description
    Text
      Let $X$ be a normal toric variety with Cox ring graded by its class group.
      This package provides commands for translating between a chamber in the secondary fan,
      the corresponding irrelevant ideal in the Cox ring, or maximal cones of the fan.

      Implemented methods allow for
      computing primitive collections and primitive relations, enumerating maximal chambers
      in the effective cone, recovering the irrelevant ideal attached to a chosen chamber,
      and reconstructing toric data from that ideal.
    Example
      needsPackage "NormalToricVarieties";
      X = smoothFanoToricVariety(2, 3)
      L = chambers X
      C = L#0;
      B = idealFromChamber(X, C)
      assert(C == chamberFromIdeal B)
      Y = normalToricVariety(rays X, effGenerators X, C)
      assert(C == nefGenerators Y)
  SeeAlso
    NormalToricVarieties
    Truncations
    Polyhedra
  Subnodes
    primitiveCollections
    primitiveRelation
    chambersFromRelation
    conesFromChamber
    idealFromChamber
    chamberFromIdeal
    Bl2PP
    movGenerators
    secondaryFan
    chambers
    secondaryFanWalls
    chamberGraph
    adjacentChambers
    conesFromIdeal
    degreeMap
    ringMap
    mapPresentation

Node
  Key
     primitiveCollections
    (primitiveCollections, NormalToricVariety)
  Headline
    compute the primitive collections of a toric variety
  Usage
    primitiveCollections X
  Inputs
    X: NormalToricVariety
  Outputs
    : List
      of minimal subsets of the rays of $X$
  Description
    Text
      A primitive collection is a minimal set of rays that is not contained in any maximal cone.
      This command returns all primitive collection for $X$.
    Example
      needsPackage "NormalToricVarieties";
      X = hirzebruchSurface 3
      primitiveCollections X
  SeeAlso
    primitiveRelation

Node
  Key
     primitiveRelation
    (primitiveRelation, NormalToricVariety, List)
  Headline
    compute the primitive relation attached to a primitive collection
  Usage
    primitiveRelation(X, I)
  Inputs
    X: NormalToricVariety
    I: List
      ray indices corresponding to a primitive collection
  Outputs
    : HashTable
  Description
    Text
      This command records the linear relation obtained by writing the sum of the rays
      in a primitive collection @TT "I"@ inside the unique cone whose relative interior contains that sum.
    Example
      needsPackage "NormalToricVarieties";
      X = hirzebruchSurface 3
      I = first primitiveCollections X
      primitiveRelation(X, I)
  SeeAlso
    primitiveCollections
    chambersFromRelation

Node
  Key
     conesFromChamber
    (conesFromChamber, List, Matrix, Matrix)
    (conesFromChamber, List, Matrix, Cone)
  Headline
    construct maximal cones from a chamber in the secondary fan
  Usage
    conesFromChamber(L, eff, nef)
  Inputs
    L: List
      of ray vectors
    eff: Matrix
      degree matrix for the rays in @TT "L"@
    nef: {Matrix, Cone}
      a chamber in the secondary fan
  Outputs
    : List
      of index sets for the maximal cones of the corresponding toric variety
  Description
    Text
      This command treats @TT "nef"@ as the nef cone for a toric variety with rays @TT "L"@
      and divisor class map @TT "eff"@, and returns the maximal cones of that variety.
      Each output list records the ray indices spanning one maximal cone.
    Example
      needsPackage "NormalToricVarieties";
      X = smoothFanoToricVariety(2, 3)
      conesFromChamber(rays X, effGenerators X, nefGenerators X)
  SeeAlso
    idealFromChamber

Node
  Key
     chambers
    (chambers, Variety)
    (chambers, Matrix)
  Headline
    list the maximal chambers in the effective cone
  Usage
    chambers X
    chambers M
  Inputs
    X: Variety
    M: Matrix
  Outputs
    : List
      of matrices whose columns span maximal chambers
  Description
    Text
      For a toric variety, this command computes the maximal cones of the secondary fan determined by
      @TO effGenerators@.  The matrix form performs the same computation directly from degree matrix.
    Example
      needsPackage "NormalToricVarieties";
      X = smoothFanoToricVariety(2, 3)
      chambers X
      effGenerators X
      chambers effGenerators X
  SeeAlso
    secondaryFan
    adjacentChambers

Node
  Key
     idealFromChamber
    (idealFromChamber, NormalToricVariety, Matrix)
    (idealFromChamber, NormalToricVariety, Cone)
    (idealFromChamber, PolynomialRing, Matrix)
    (idealFromChamber, PolynomialRing, Cone)
  Headline
    compute the irrelevant ideal attached to a chamber
  Usage
    idealFromChamber(X, C)
    idealFromChamber(S, C)
  Inputs
    X: NormalToricVariety
    S: PolynomialRing
    C: {Matrix, Cone}
  Outputs
    : Ideal
  Description
    Text
      This command treats @TT "C"@ as the nef cone and reconstructs
      the corresponding irrelevant ideal in the Cox ring.
    Example
      needsPackage "NormalToricVarieties";
      X = smoothFanoToricVariety(2,3)
      idealFromChamber(X, nefGenerators X)
  SeeAlso
    chamberFromIdeal
    conesFromChamber

Node
  Key
     chamberFromIdeal
    (chamberFromIdeal, Ideal)
  Headline
    recover a chamber from an irrelevant ideal
  Usage
    chamberFromIdeal B
  Inputs
    B: Ideal
  Outputs
    : Cone
  Description
    Text
      The chamber is reconstructed by intersecting the cones generated by
      the degrees of the variables occurring in each minimal generator of @TT "B"@.
    Example
      needsPackage "NormalToricVarieties";
      X = smoothFanoToricVariety(2, 3)
      chamberFromIdeal ideal X
  SeeAlso
    idealFromChamber

Node
  Key
     Bl2PP
    (Bl2PP, ZZ)
    [Bl2PP, Variable]
    [Bl2PP, CoefficientRing]
  Headline
    construct the blowup of projective space at two torus-fixed points
  Usage
    Bl2PP n
  Inputs
    n: ZZ
  Outputs
    : NormalToricVariety
    CoefficientRing => Ring
    Variable => Symbol
  Description
    Text
      This command constructs the toric variety obtained by blowing up $\PP^n$
      at two torus-fixed points. The grading on the Cox ring is chosen using
      the degree matrices from Example 4.7 of @arXiv "2501.00130"@.
    Example
      X = Bl2PP(5)
      effGenerators X
      nefGenerators X
      chamberGraph X
  SeeAlso
    normalToricVariety
    chambers
    effGenerators

Node
  Key
    (normalToricVariety, List, Ideal)
    (normalToricVariety, List, Matrix, Cone)
    (normalToricVariety, List, Matrix, Matrix)
    (normalToricVariety, List, PolynomialRing, Cone)
    (normalToricVariety, List, PolynomialRing, Matrix)
    (normalToricVariety, NormalToricVariety, Cone)
    (normalToricVariety, NormalToricVariety, Ideal)
    (normalToricVariety, NormalToricVariety, Matrix)
  Headline
    construct birational toric variety given chamber data
  Description
    Text
      As an example, we consider the toric varieties with the same rays as $\PP^5$ blown up at two points.
    Example
      X0 = Bl2PP(5);
      S = ring X0;
      A = rays X0;
      eff = effGenerators X0
      L = chambers X0
  Synopsis
    Usage
      normalToricVariety(rayList, irr)
    Inputs
      rayList:List -- of ray vectors of the toric variety
      irr:Ideal
        an irrelevant ideal in a polynomial ring $S$
	with the same number of variables as the given rays
    Outputs
      :NormalToricVariety
        a toric variety with the given rays and degree matrix of $S$
        corresponding to the given irrelevant ideal
    Description
      Example
        B = idealFromChamber(X0, L#4)
        assert(nefGenerators normalToricVariety(A, B) == L#4)
  Synopsis
    Usage
      normalToricVariety(rayList, eff, nef)
    Inputs
      rayList:List      -- of ray vectors of the toric variety
      S:PolynomialRing  -- the Cox ring of the toric variety
      eff:Matrix        -- the degree matrix of the toric variety
      nef:{Matrix,Cone} -- a chamber in the secondary fan of the given degree matrix
    Outputs
      :NormalToricVariety
        a toric variety with given rays and degree matrix
        corresponding to the given nef chamber in the secondary fean
    Description
      Example
	assert(nefGenerators normalToricVariety(A, eff, L#1) == L#1)
	assert(nefGenerators normalToricVariety(A, S,   L#3) == L#3)
      Example
        C = coneFromVData L#2;
	assert(nefGenerators normalToricVariety(A, eff, C) == L#2)
	assert(nefGenerators normalToricVariety(A, S,   C) == L#2)
  Synopsis
    Usage
      normalToricVariety(X, irr)
      normalToricVariety(X, nef)
    Inputs
      X:NormalToricVariety
      irr:Ideal         -- an irrelevant ideal for a toric variety with the same rays
      nef:{Matrix,Cone} -- a chamber in the secondary fan of the toric variety
    Outputs
      :NormalToricVariety
        a toric variety with the same rays and degree matrix
        but with the given nef cone or irrelevant ideal
    Description
      Example
	assert(nefGenerators normalToricVariety(X0, B)   == L#4)
	assert(nefGenerators normalToricVariety(X0, C)   == L#2)
	assert(nefGenerators normalToricVariety(X0, L#3) == L#3)
  SeeAlso
    chambers
    conesFromChamber
    conesFromIdeal
    effGenerators
    nefGenerators

Node
  Key
     movGenerators
    (movGenerators, NormalToricVariety)
    (movGenerators, Matrix)
  Headline
    compute generators for the moving cone
  Usage
    movGenerators X
    movGenerators M
  Inputs
    X: NormalToricVariety
    M: Matrix
      degree matrix
  Outputs
    : Matrix
      whose columns generate the moving cone
  Description
    Text
      The moving cone is computed as the intersection of the cones obtained
      by deleting one column at a time from the effective cone generators.
    Example
      needsPackage "NormalToricVarieties";
      X = smoothFanoToricVariety(2, 3)
      movGenerators X
      movGenerators effGenerators X
  SeeAlso
    secondaryFan
    chambers

Node
  Key
     secondaryFan
    (secondaryFan, Variety)
    (secondaryFan, Matrix)
  Headline
    construct the secondary fan
  Usage
    secondaryFan X
    secondaryFan M
  Inputs
    X: Variety
    M: Matrix
      degree matrix
  Outputs
    : Fan
  Description
    Text
      This command packages the chambers determined by the effective cone into a fan.
      The maximal cones of the result are exactly the chambers returned by @TO chambers@.
    Example
      needsPackage "NormalToricVarieties";
      X = smoothFanoToricVariety(2, 3)
      secondaryFan effGenerators X
      secondaryFan X
  SeeAlso
    chambers
    movGenerators

Node
  Key
     secondaryFanWalls
    (secondaryFanWalls, Variety)
    (secondaryFanWalls, Matrix)
  Headline
    record how walls sit inside maximal chambers
  Usage
    secondaryFanWalls X
    secondaryFanWalls M
  Inputs
    X: Variety
    M: Matrix
      degree matrix
  Outputs
    : HashTable
  Description
    Text
      The keys are codimension-one walls of the maximal chambers in the secondary fan,
      stored as matrices whose columns span the wall.
      The value of a wall is the list of maximal chambers containing it.
      Boundary walls therefore occur in one chamber and interior walls in two.
    Example
      needsPackage "NormalToricVarieties";
      secondaryFanWalls Bl2PP(5)
  SeeAlso
    chambers
    chamberGraph
    adjacentChambers

Node
  Key
     chamberGraph
    (chamberGraph, Variety)
    (chamberGraph, Matrix)
  Headline
    construct the adjacency graph of maximal chambers
  Usage
    chamberGraph X
    chamberGraph M
  Inputs
    X: Variety
    M: Matrix
      degree matrix
  Outputs
    : Graph
  Description
    Text
      The keys are maximal chambers in the secondary fan and the values are the lists
      of chambers sharing a codimension-one wall with them.
    Example
      needsPackage "NormalToricVarieties";
      chamberGraph Bl2PP(5)
  SeeAlso
    chambers
    secondaryFanWalls
    adjacentChambers

Node
  Key
     adjacentChambers
    (adjacentChambers, NormalToricVariety, Matrix)
    (adjacentChambers, NormalToricVariety, Cone)
  Headline
    find chambers and walls adjacent to a given chamber
  Usage
    adjacentChambers(X, C)
  Inputs
    X: NormalToricVariety
    C: {Matrix, Cone}
  Outputs
    : HashTable
  Description
    Text
      The keys are the adjacent chambers and boundary walls meeting @TT "C"@,
      and the values are the corresponding common faces with @TT "C"@.
    Example
      needsPackage "NormalToricVarieties";
      X = hirzebruchSurface 4
      adjacentChambers(X, nefGenerators X)
  SeeAlso
    chambers
    chambersFromRelation

Node
  Key
     conesFromIdeal
    (conesFromIdeal, Ideal)
  Headline
    recover maximal cones from an irrelevant ideal
  Usage
    conesFromIdeal B
  Inputs
    B: Ideal
      a nonzero irrelevant ideal
  Outputs
    : List
      of index sets for the maximal cones
  Description
    Text
      For each monomial generator of @TT "B"@, the variables not appearing in that generator
      determine one maximal cone. The output is therefore a list of ray-index sets that can
      be passed to @TO normalToricVariety@.
    Example
      needsPackage "NormalToricVarieties";
      X = smoothFanoToricVariety(2, 3)
      conesFromIdeal ideal X
  SeeAlso
    chamberFromIdeal

-- TODO:
-- Node
--   Key
--     degreeMap
--     (degreeMap,NormalToricVariety,NormalToricVariety)
--     ringMap
--     (ringMap,NormalToricVariety,NormalToricVariety)
--     mapPresentation
--     (mapPresentation,RingMap,Module,Matrix)
--     (mapPresentation,NormalToricVariety,NormalToricVariety,Module)
--   Headline
--     construct maps induced by wall-crossing in the secondary fan
--   Usage
--     degreeMap(Y,X)
--     ringMap(Y,X)
--     mapPresentation(Y,X,M)
--   Inputs
--     Y: NormalToricVariety
--     X: NormalToricVariety
--     M: Module
--   Outputs
--     : Thing
--       depending on whether @TT "degreeMap"@, @TT "ringMap"@, or @TT "mapPresentation"@ is called
--   Description
--     Text
--       When the rays of @TT "Y"@ form a sublist of the rays of $X$, these commands build the induced
--       map on divisor class gradings, the Cox ring homomorphism, and the transported presentation of @TT "M"@.
--     Example
--      needsPackage "NormalToricVarieties";
--       X = hirzebruchSurface 3
--       B = idealFromChamber(X, first chambers X)
--       Y = normalToricVariety(rays X, conesFromIdeal trim B, WeilToClass => effGenerators X)
--       degreeMap(Y,X)
--       ringMap(Y,X)
///

--------------------------------------------------------------------------------
-- Development
--------------------------------------------------------------------------------
end--

restart
needsPackage "Chambers"
X = smoothFanoToricVariety(2, 3)
X = hirzebruchSurface 3
S = ring X

P = primitiveCollections X
R = primitiveRelation_X \ P
C = chambersFromRelation_X \ R
Bs = (ell -> idealFromChamber_X \ ell) \ keys \ C

Y = normalToricVariety(X, Bs_0_0)
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
restart
needsPackage "Chambers"

needs "helpers.m2"
needs "truncate.m2"

-- scan(125, i -> print(i, movGenerators fano(4,i) != nefGenerators fano(4,i)))

X = fano(4, 8) -- and fano(4,15), and more?
X = hirzebruchSurface 3
S = ring X
L = chambers X
B = idealFromChamber(X, L#0)
X' = normalToricVariety(rays X, B)
assert(effGenerators X' * matrix rays X' == 0)
S' = ring X'
assert not isFano X' -- cool!
netList{decompose ideal X, decompose ideal X'}

(C0, C1) = (coneFromVData L#0, coneFromVData L#1)

mahrud({-3,-3}, {3,3}, (i,j) -> # unique degrees truncate({i,j}, S', symbol Cone => C0))
mahrud({-3,-3}, {3,3}, (i,j) -> # unique degrees truncate({i,j}, S,  symbol Cone => C1))

rays C1
movGenerators X
effGenerators X
d = {1, 1}; netList supportOfTor res(S^{d}  ** module truncate(d, S,  symbol Cone => C1))
d = {-1, 3}; netList supportOfTor res(S'^{d} ** module truncate(d, S', symbol Cone => C0))

---
netList apply(L, chamb -> (
	C := coneFromVData chamb;
	d := 2 * first vecs interiorVector C;
	supportOfTor res(S^{d} ** module truncate(d, S, symbol Cone => C))
	))

-- TODO: is this correct?
nefFromIdeal = B -> rays intersection apply(unique \\ indices \ B_*, e -> coneFromVData degs_e)

restart
needsPackage "Chambers"
installPackage "Chambers"
