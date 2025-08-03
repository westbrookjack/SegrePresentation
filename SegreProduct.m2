-- -*- coding: utf-8 -*-

needsPackage "Normaliz"

newPackage(
    "SegrePresentation",
    Version => "0.1",
    Date => "August 3, 2025",
    Headline => "A package that computes presentations for Segre products.",
    Authors => {{ Name => "Jack Westbrook", Email => "jackswestbrook@gmail.com", HomePage => "https://westbrookjack.github.io/"}},
    Keywords => {"Segre", "presentation", "commutative algebra"},
    AuxiliaryFiles => false,
    DebuggingMode => false,
    PackageImports => {"Polyhedra"}
)


export {"segrePresentation", "VariableName"}

segrePresentation = method(Options => {VariableName => "p"});

segrePresentation(Ring, Ring) := o -> (R, S) -> (
    if not isRing R and isRing S then error "Both R and S must be rings";
    if not (isHomogeneous R and isHomogeneous S) then error "Both R and S must be graded rings";
    if not (coefficientRing R === coefficientRing S) then error "R and S must have identical coefficient rings";
    
    vPrefix := o#VariableName;
    Rgens := gens R;
    m := #Rgens;
    Sgens := gens S;
    n := #Sgens;
    K := coefficientRing R;
    weightList := new List;

    for gen in Rgens do (
        deg := degree gen;
        if #(deg) != 1 then error "Multidegrees for variables in R not supported";
        weightList = append(weightList, deg#0);
    );
    for gen in Sgens do (
        deg := degree gen;
        if #(deg) != 1 then error "Multidegrees for variables in S not supported";
        weightList = append(weightList, -1*(deg#0));
    );
    
    M := matrix {weightList};
    I := id_(ZZ^(m+n));
    C := coneFromHData(I, M);
    H := hilbertBasis C;

    genPolyRing := (r) -> K[apply(1..r, i -> value(vPrefix | "_" | toString i))];
    SegreRing := genPolyRing(#H);
    tensorRing := R ** S;
    if numgens tensorRing != m+n then
        error "# of generators of the tensor product of R and S is not equal to the sum of the numbers of generators";
    
    relList := {};
    for elt in H do (
        monomial := 1;
        for i to m+n-1 do (
            monomial *= (tensorRing_i)^(elt_(i,0));
        );
        relList = append(relList, monomial);
    );
    relationsMap := map(tensorRing, SegreRing, relList);
    
    
    (relationsMap, SegreRing/kernel relationsMap)
);

beginDocumentation()

doc ///
Key
  SegrePresentation
Headline
  Computes presentations of Segre products of weighted graded rings
Description
  Text
    This package computes a presentation of the Segre product.
///

doc ///
Key
  segrePresentation
Headline
  Computes a presentation for the Segre product of two graded rings
Usage
  segrePresentation(R, S)
Inputs
  R:Ring -- a graded ring
  S:Ring -- a graded ring
Outputs
  (phi, presRing):List
    phi:Map -- a surjective ring homomorphism onto {\t R#S} contained in {\t R**S}, such that its source modulo its kernel is a presentation of the Segre product
    presRing -- a presentation of the Segre product {\t R#S}
Description
  Text
    Returns a presentation of the Segre product of R and S.
  Example
    R = QQ[x, y, z];
    S = QQ[a, b]/ideal(a^2);
    (f, P) = veronesePresentation(R, S);
    f -- the map
    P -- the quotient ring
Acknowledgement
  This code was partially created during the 2025 REU program in mathematics at the University of Michigan, Ann Arbor.
Contributors
  Austyn Simpson
///

end