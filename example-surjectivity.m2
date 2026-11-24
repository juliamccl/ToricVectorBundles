needsPackage "ToricVectorBundles2"

A2 = affineSpace 2

EE = lineBundle(-A2_0) ++ lineBundle(-A2_1)
filtrations EE

OA2 = trivialBundle(A2,1)

p = map(OA2,EE, matrix {{1,1}})
isWellDefined p

-- "reflexive cokernel":
cokernel p 

-- WRONG, the true cokernel is the skyscraper sheaf at 0:
isSurjective p 

------------------------

isSurjective2 := p -> (
	EE = source p;
	FF = target p;
	X = variety EE;
	
	minE = min apply(filtrationJumps EE, min );
	minF = min apply(filtrationJumps FF, min );

	Emat = filteredPiece(EE,(rays X)#0,minE);
	Fmat = filteredPiece(FF,(rays X)#0,minF);
	-- Comment: it would be faster if we break once one is false, wouldn't it?
	return all for d in 1..dim X list (
		all for sigma in cones(d,fan X) list (
			minE = min apply(sigma, r -> min filtrationJumps(EE,(rays X)#r) );
			minF = min apply(sigma, r -> min filtrationJumps(FF,(rays X)#r) );
			minEF = min {minE,minF}+1;
			maxE = max apply(sigma, r -> max filtrationJumps(EE,(rays X)#r) );
			maxF = max apply(sigma, r -> max filtrationJumps(FF,(rays X)#r) );
			maxEF = max {maxE,maxF};
			all for i in minEF..maxEF list (
				Ei = intersect(apply(sigma, r -> image filteredPiece(EE,(rays X)#r,i)));
				Fi = intersect(apply(sigma, r -> image filteredPiece(FF,(rays X)#r,i)));
				mati = (matrix p)*Emat*(gens Ei);
				image mati == Fi
			)
		)
	)
)

-------------------------

isSurjective2 p

		
