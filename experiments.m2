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
X = toricProjectiveSpace 2

-- Get the fan of the toric variety
secondaryFan1 = X -> (
    fanX := fan X;
    raysX := rays X;
-- Extract the rays (as a matrix where columns are rays)
-- Get the maximal cones
    maxConesX := max X;
-- For the secondary fan, we need the polytope associated to -K_X
-- Get the polytope from the anticanonical divisor
    P := polytope X;
-- Compute vertices of the polytope
V := vertices P;


-- The secondary polytope is computed from the regular subdivisions
-- This requires the Polyhedra package
-- Get the secondary polytope
secondaryPolytope := secondaryPolytope V;
-- The secondary fan is the normal fan of the secondary polytope
normalFan secondaryPolytope
)

idealsFromGrading = method()
idealsFromGrading NormalToricVariety := X ->(
    R := rays X;
    C := transpose syz transpose matrix rays X;
    r := dim X;
    S := ring X;
    C' = unique apply(numcols C, i -> flatten entries C_{i});
    possibleDegs = toList subsets(set C', r)/toList;
    <<C'<<endl;
    sums := unique for V in possibleDegs list sum V;
    <<sums<<endl;
    rads := unique for s in sums list(
       radical ideal truncate (s,S));
    rads/decompose
    )



///
restart
load "experiments.m2"
--viewHelp NormalToricVariety
X = hirzebruchSurface(3)
II = idealsFromGrading X
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


