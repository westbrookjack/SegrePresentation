--! \file SegreProduct.m2
--! \brief Package for computing the presentation of the Segre product of two rings.
--!
--! This package provides the function \code{segrePresentation} which computes a presentation
--! for the Segre product of two algebras of finite type over the same field.
--!
--! Both input rings must be either quotient rings or polynomial rings over the same coefficient field.
--! Additionally, the degrees of all generators must be single integers (i.e. unigraded).
--!
--! \remark
--! When the coefficient ring is a Galois field, for some reason there is an extra variable in the
--! returned map corresponding to the chosen multiplicative generator.
--!
--! \author Jack Westbrook
--! \date 2025-04-04

-*
 * segrePresentation(R,S)
 * 
 * Returns a presentation for the Segre product of the two rings R and S.
 *
 * Both R and S must be either quotient rings or polynomial rings over the same field.
 * The degrees of all generators must be one-dimensional.
 *
 * The function returns a list:
 * 
 * - The first element is the ring map from the tensor product ring to the Segre ring.
 * - The second element is the Segre product ring, given as the quotient of the Segre ring by the kernel of the map.
 *
 * @param R a polynomial or quotient ring
 * @param S a polynomial or quotient ring with the same coefficient field as R
 * @return a list containing the map and the presentation of the Segre product.
 *-


segrePresentation = (R, S) -> (
    if not ((isQuotientRing S or isPolynomialRing S) and (isQuotientRing R or isPolynomialRing R)
            and coefficientRing R === coefficientRing S) then
        error "R and S must be algebras of finite type over the same field";
    
    weightList = {};
    Rgens = gens R;
    m = length Rgens;
    Sgens = gens S;
    n = length Sgens;
    K = coefficientRing R;
    
    for gen in Rgens do (
        if not (length(degree gen) == 1) then error "Generators of R must have single degree entries.";
    );
    for gen in Sgens do (
        if not (length(degree gen) == 1) then error "Generators of S must have single degree entries.";
    );
    
    for elt in Rgens do (
        weightList = append(weightList, (degree elt)#0);
    );
    for elt in Sgens do (
        weightList = append(weightList, -1 * ((degree elt)#0));
    );
    
    M = matrix {weightList};
    I = id_(ZZ^(m+n));
    C = coneFromHData(I, M);
    H = hilbertBasis C;
    l = length H;
    SegreRing = K[s_1 .. s_l];
    tensorRing = R ** S;
    tensorGens = gens tensorRing;
    if not (length(tensorGens) == m+n) then
        error "# of generators of the tensor product of R and S is not equal to the sum of the numbers of generators";
    
    relList = {};
    for elt in H do (
        monomial = 1;
        for i to m+n-1 do (
            monomial = monomial * (tensorGens#i)^(elt_(i,0));
        );
        relList = {monomial} | relList;
    );
    relationsMap = map(tensorRing, SegreRing, relList);
    
    -- Compute the kernel of the map
    kerRelationsMap = kernel relationsMap;
    
    -- Define the Segre product as the quotient of the tensor product by this kernel
    return {relationsMap, SegreRing/kerRelationsMap};
)

-- Export the function so it is available when the package is loaded.
export segrePresentation
