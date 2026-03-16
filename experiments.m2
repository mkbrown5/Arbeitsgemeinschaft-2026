-- Experiments toward the secondary fan;
-- work with Daniel Erman, February 2026

needsPackage "NormalToricVarieties"
needsPackage "Truncations"
needsPackage "Polyhedra"
needsPackage "Chambers"

nonProjective = () ->(
    R := {
    { 0,  0,  1}, -- v1
    {4, 0 ,1},   --v2
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


    

-- Load necessary packages


-- Example: Start with a normal toric variety
-- Let's use P^2 as a simple example
///
restart
load "experiments.m2"
X = toricProjectiveSpace 2
secondaryFan X
rays oo
-- Get the fan of the toric variety
X = hirzebruchSurface 3
secondaryFan X
secondaryFan1 = X -> (
    fanX := fan X;
    raysX := rays X;
-- Extract the rays (as a matrix where columns are rays)
-- Get the maximal cones
    maxConesX := max X;
-- For the secondary fan, we need the polytope associated to -K_X
-- Get the polytope from the anticanonical divisor
    P := polytope (-toricDivisor X);
-- Compute vertices of the polytope
V := vertices P;
-- The secondary polytope is computed from the regular subdivisions
-- This requires the Polyhedra package
-- Get the secondary polytope
statePolytope P
Q = secondaryPolytope P
-- The secondary fan is the normal fan of the secondary polytope
normalFan Q
vertices Q
)
///
idealsFromGrading = method()
idealsFromGrading NormalToricVariety := X ->(
    R := rays X;
    r := dim X;
    S := ring X;
    C := unique degrees S;
    pr := dim S -r;
    possibleDegs := toList (
	subsets(set C,pr)/toList);
    possibleIndependent = select(possibleDegs, V ->
	det matrix V != 0);
    sums := unique for V in possibleIndependent list sum V;

    rads := unique for s in sums list(
s = {1,2,-1}
    p := 1;
    d := 0;
    while d < r do(
    p = p+1;
    f := flatten entries basis((p*s,S));
    ff := flatten (f/exponents);
    fm := matrix for i from 1 to #ff-1 list ff_i - ff_0;
    d = rank fm;
    );
    radical ideal (basis(p*s,S))
    );
    rads/decompose
    )



///
radical ideal basis ({-3,2}, S)
radical truncate({-3,2}, S)

restart
load "experiments.m2"
--viewHelp NormalToricVariety
X = hirzebruchSurface(5)
X = smoothFanoToricVariety(2,3)
rays X
degrees ring X
elapsedTime II = idealsFromGrading X
netList II
cham = chambers X
decompose idealFromChamber(X,cham#1)
elapsedTime secondaryFan X
netList II
--what was the vector that gave P(1,1,2) Monday?

ideal X
chambers X
netList for c in chambers X list decompose idealFromChamber (X,c)
///
end--

restart
load "experiments.m2"
X = nonProjective()
isComplete X
isProjective X

S = ring X
netList degrees S
netList decompose ideal X
nefGenerators X
viewHelp NormalToricVarieties
gfanSecondaryFan X


-- Display information about the secondary fan
print("Rays of secondary fan:")
print rays secondaryFan

print("Maximal cones of secondary fan:")
print maxCones secondaryFan

print("Dimension of secondary fan:")
print dim secondaryFan
For a more complete example with a non-trivial toric variety:
macaulay2needsPackage "NormalToricVarieties"
needsPackage "Polyhedra"

-- Create a Hirzebruch surface F_2

raysF2 = {{1,0},{0,1},{-1,2},{0,-1}}
maxConesF2 = {{0,1},{1,2},{2,3},{0,3}}
F2 = normalToricVariety(raysF2, maxConesF2)
D = toricDivisor({1,0,0,1}, F2)
-- Get the polytope
P = polytope D
V = vertices P

-- Compute secondary polytope and fan
viewHelp secondaryPolytope
SP = secondaryPolytope P
SF = normalFan SP
vertices SP
rays SF -- this doesn't look like what we computed by hand.

-- Analyze the secondary fan
print("Number of rays in secondary fan: " | toString(numColumns rays SF))
print("Number of maximal cones: " | toString(#maxCones SF))
print("Dimension: " | toString(dim SF))


--- Erman's code using Chambers.m2
restart
needsPackage "NormalToricVarieties"
X = hirzebruchSurface(3)
load "Chambers.m2"
L = chambers X
B0 = idealFromChamber(X, L#0)
X0 = normalToricVariety(rays X, conesFromIdeal trim B0, WeilToClass => effGenerators X)
degrees ring X0
decompose ideal X0
--X0 is the weighted P(1,1,3)

B1 = idealFromChamber(X, L#0)
X1 = normalToricVariety(rays X, conesFromIdeal trim B1, WeilToClass => effGenerators X)
degrees ring X1
decompose ideal X1
--X1 is the Hirzebruch surface

--given a ntv X, of dimension r with n rays v_i,
list: every r-tuple of rays V  with nonzero det,
an interior ray gamma_V
    (refinement: take a multiple, perturb
    with small multiples of other rays. This would make
    the result more likely correct, but slow the
    computation)
return the radical of the truncation of
S_{\gea gamma_F}

X3 = hirzebruchSurface 3
X4 = hirzebruchSurface 4
X = X3**X4
X = smoothFanoToricVariety(3,10)
X = nonProjective()
isWellDefined X
dim X
picardGroup X
elapsedTime sF = secondaryFan X
rays sF
maxCones sF
rays oo
elapsedTime chambers X


----Thomsen collection?
X = hirzebruchSurface 3
#rays X
D = toricDivisor({1,0,0,0}, X)

F = map(X,X,matrix{{2,0},{0,2}})

viewHelp ccRefinement
code methods ccRefinement

X = nonProjective()
D = transpose matrix degrees ring X
elapsedTime ccRefinement D

---
--embedding of an elliptic curve in
--P^(r-1) x P^(s-1)
--by the maps corresponding to
--r*p1 and s*p2, where p1,p2 are points.
restart
--(r,s) embedding

restart
degs = (r,s) -> toList (r:{1,0}) |
                toList(s:{0,1})
(r,s) = (3,4)
kk= ZZ/32003
P2 = kk[x,y,z,h,
     Degrees =>{{1,0},{1,0},{1,0},{-1,1}}]
f = y^2*z-x*(x-z)*(x+z)
E = P2/f
p1 = ideal(x,y)
p2 = ideal(x-z, y)
--p2 =p1
for i from 1 to 10 list isIsomorphic(module(p1^i), module(p2^i))

D1 = ideal image basis({r,0},(ideal (p1^r)_0:p1^r))
D2' = ideal image basis({s,0},(ideal (p2^s)_0:p2^s))
D2 = h^s*D2'

PP = kk[a_0..a_(r-1),b_0..b_(s-1),
    Degrees => degs(r,s)]

toE = map(E, PP, gens D1|gens D2,
    DegreeMap => x ->{r*x_0, s*x_1})
I = ker toE
isHomogeneous I
bI = minimalBetti I
codim I
rI = res I
tally apply(length rI+1, i-> degrees rI_i)

