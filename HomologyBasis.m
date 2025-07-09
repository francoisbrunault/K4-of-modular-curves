// Magma code to compute bases of modular symbols
// and convert them in PARI/GP-readable form.

// Convert a modular symbol to a linear combination
// of Manin symbols in PARI/GP-readable form.
//
// Output: a sequence of sequences [n, a, b, c, d]
// meaning the sum of the n {h.0, h.oo} with
// h = [a, b; c, d] in SL_2(Z).

ModSymConvert := function(xi)
  Z := Integers();
  Q := Rationals();
  z := ModularSymbolRepresentation(xi);
  denom := Lcm([Denominator(Q!x[1]) : x in z]);
  L := [];
  for x in z do
    x1 := Z!(denom*x[1]);
    x2 := x[2];
    a := Z!x2[2][1];
    c := Z!x2[2][2];
    b := Z!x2[1][1];
    d := Z!x2[1][2];
    if Abs(a*d-b*c) ne 1 then
      error "Determinant", a*d-b*c, "not equal to +/- 1";
    end if;
    if a*d-b*c eq 1 then
      Append(~L, [x1, a, b, c, d]);
    else
      Append(~L, [x1, a, -b, c, -d]);
    end if;
  end for;
  return L;
end function;

// Compute a basis of the (+1)-part of the homology of X_1(N)

HomologyBasisX1 := function(N)
  M := ModularSymbols(Gamma1(N), 2, +1);
  S := CuspidalSubspace(M);
  B := IntegralBasis(S);
  return [ModSymConvert(xi) : xi in B];
end function;



// Write in "file" the sequence of bases of the (+1)-part of homology of X_1(N) for levels N between N1 and N2.
// NB. Magma represents the (+1)-part of homology of X_1(N) not as the invariants of complex conjugation, but as the coinvariants.

WriteHomologyBasisX1 := procedure(file, N1, N2)
  Write(file, "{\ngammaNdata =");
  Write(file, [HomologyBasisX1(N) : N in [N1..N2]]);
  Write(file, "};");
end procedure;

// WriteHomologyBasisX1("DataH1", 1, 50);



// Write in "file" the sequence of Cremona labels of elliptic curves of conductor between N1 and N2 (up to isogeny), and the sequence of associated Hecke-eigen modular symbols in the (+1)-part of homology of X_1(N).

WriteHomologyBasisEll := procedure(file, N1, N2)
  L_E := [];
  L_xi := [];
  for N := N1 to N2 do
    M := ModularSymbols(Gamma1(N), 2, +1);
    S := CuspidalSubspace(M);
    Snew := NewSubspace(S);
    Mf_list := NewformDecomposition(Snew);
    for Mf in Mf_list do
      if BaseField(Mf) eq Rationals() and Dimension(Mf) eq 1 then
        E := EllipticCurve(Mf);
        lbl := "\"" cat CremonaReference(E) cat "\"";
        Append(~L_E, lbl);
        xi := IntegralBasis(Mf)[1];
        Append(~L_xi, ModSymConvert(xi));
      end if;
    end for;
  end for;
  Write(file, "{\nEdata =");
  Write(file, L_E);
  Write(file, "};");
  Write(file, "\n{\ngammaEdata =");
  Write(file, L_xi);
  Write(file, "};");
end procedure;

// WriteHomologyBasisEll("DataH1ell", 1, 100);
