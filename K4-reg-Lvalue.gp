/***************************************************/
/* COMPUTATION OF K_4 REGULATORS ON MODULAR CURVES */
/* IN TERMS OF L-VALUES OF MODULAR FORMS           */
/***************************************************/

/*

Author: François Brunault
Date: May 2023

To use this program, you should start PARI/GP in the
directory containing this file, and type the command

\r K4-reg-Lvalue.gp

This program computes in exact form the Goncharov
regulator of the classes xi(a,b) in K_4 of the modular
curve Y(N) for generic elliptic parameters a,b in
(Z/NZ)^2. It is based on Theorem 1 of the article

[BZ23] F. Brunault, W. Zudilin, Modular regulators and multiple Eisenstein values, arXiv:2303.15554

Please see the description of the main function G_reg
below for more details.

The program can be used to perform the computations
described in Section 6 ('Final computation') of the paper

[B23] F. Brunault, On the Mahler measure of (1+x)(1+y)+z

To launch these computations, type

final_computation()

To compute the Goncharov regulator G(a,b) defined in
the introduction of [BZ23], with a, b in (Z/NZ)^2,
the command is Gab(N, a, b). For example:

Gab(6, [1, 2], [1, 2])

See the description of the function Gab for the
meaning of the output.

More generally, the function G_reg can integrate
the regulator of a linear combination of cocycles
xi(a,b), along an arbitrary modular symbol.

*/


/*********************/
/* EISENSTEIN SERIES */
/*********************/

\\  The function GkN(k, N, [x1, x2], B) gives the
\\  Eisenstein series with rational Fourier coefficients
\\
\\  G^{(k);N}_{x1,x2}
\\
\\  from the introduction of [BZ23], as a power
\\  series in x = q^{1/N} with precision O(x^B)
\\  (by default B = 20*N).

{
GkN(k, N, X, B = 20*N) =
  my([x1, x2] = X%N, x1_0, x2_0, a0, G, m, n);
  if(k < 1, error("The weight must be >= 1"));
  if(k == 1,
    if(x1 == 0 && x2 != 0,
      a0 = 1/2 - x2/N);
    if(x1 != 0 && x2 == 0,
      a0 = 1/2 - x1/N));
  if(k >= 2,
    if(x2 == 0,
      a0 = -N^(k-1) * subst(bernpol(k), x, x1/N)/k));
  G = vector(B-1);
  x1_0 = if(x1 == 0, N, x1);
  x2_0 = if(x2 == 0, N, x2);
  for(i = 0, ceil((B/x2_0 - x1_0)/N)-1,
    m = x1_0 + i*N;
    for(j = 0, ceil((B/m - x2_0)/N)-1,
      n = x2_0 + j*N;
      G[m*n] += m^(k-1)));
  for(i = 1, ceil((B/(N-x2) + x1)/N)-1,
    m = i*N - x1;
    for(j = 1, ceil((B/m + x2)/N)-1,
      n = j*N - x2;
      G[m*n] += (-1)^k * m^(k-1)));
  Ser(concat(a0, G), 'x);
}

/********************/
/* THE L-VALUE PART */
/********************/

\\  The function Lab computes the L-value part in
\\  the formula of Theorem 1 of [BZ23] for the
\\  Goncharov regulator G(a,b) with a, b in (Z/NZ)^2.
\\
\\  Input:
\\
\\  * the level N
\\  * the parameters a = [a1, a2] and b = [b1, b2]
\\  * the precision B (by default B = 20*N)
\\
\\  Output:
\\
\\  a modular form F of weight 2 and level Gamma(N)
\\  given as a power series in x = q^(1/N) with
\\  precision O(x^B) such that the L-value part of
\\  G(a,b) is pi^2 * L'(F, -1).

{
Lab(N, a, b, B = 20*N) =
  my([a1, a2] = a, [b1, b2] = b);
  3/N * (GkN(1, N, [a1, b2], B) * GkN(1, N, [b1, -a2], B) + GkN(1, N, [a1, -b2], B) * GkN(1, N, [b1, a2], B));
}

/********************/
/* THE ZETA(3) PART */
/********************/

\\ Bernoulli polynomials B_1 and B_2

{
B1(x) =
  frac(x) - 1/2;
}

{
B2(x) =
  my(t = frac(x));
  t^2 - t + 1/6;
}

\\  The function z3ab computes the zeta(3) part in
\\  the formula of Theorem 1 of [BZ23] for the
\\  Goncharov regulator G(a,b) with a, b in (Z/NZ)^2.
\\
\\  Input:
\\
\\  * the level N
\\  * the parameters a = [a1, a2] and b = [b1, b2]
\\
\\  Output:
\\
\\  a rational number r such that the zeta(3) part in
\\  G(a,b) is r * zeta(3).

{
z3ab(N, a, b) =
  my([a1, a2] = a/N, [b1, b2] = b/N);
  -1/4 * (B2(a1) + B2(b1) + 4*B1(a1)*B1(b1) - B2(a2) - B2(b2) - 4*B1(a2)*B1(b2));
}

/*****************/
/* MAIN FUNCTION */
/*****************/

\\  The function G_reg computes the regulator
\\  integral of a cocycle in the Goncharov
\\  complex of Y(N) along a modular symbol.
\\
\\  Input:
\\
\\  * the level N
\\  * a vector xi of 3-component vectors [n, a, b]
\\    where n is a rational number and a, b in (Z/NZ)^2
\\    are represented as 2-component vectors of integers.
\\    The vector xi represents the cocycle
\\    \sum n * \xi(a,b)
\\    in the Goncharov complex of Y(N)
\\  * a vector gam of 2-component vectors [n, g]
\\    where n is a rational number and g is a 2x2 integral
\\    matrix [a, b; c, d] which is invertible modulo N.
\\    The vector gam represents the modular symbol
\\    \sum n * {g.0, g.oo}
\\    in the homology of X(N) relative to the cusps.
\\  * the precision B (by default B = 20*N)
\\
\\  Output: a vector [F, r], where
\\
\\  * F is a modular form of weight 2 and level Gamma(N),
\\    given as a power series in x = q^(1/N) with
\\    rational coefficients and precision O(x^B)
\\  * r is a rational number
\\
\\  meaning that the regulator integral of xi along
\\  gam equals
\\
\\  pi^2 * L'(F, -1) + r * zeta(3)
\\
\\  An error will occur if the parameters do not satisfy
\\  the genericity conditions given in Theorem 1 of [BZ23].

{
G_reg(N, xi, gam, B = 20*N) =
  my(F, r, a, b, g, ag, bg, cg);
  for(i = 1, #xi,
    [a, b] = xi[i][2..3];
    for(j = 1, #gam,
      g = gam[j][2];
      ag = (a*g)%N;
      bg = (b*g)%N;
      cg = (-ag-bg)%N;
      if(ag[1] == 0 || ag[2] == 0 || bg[1] == 0 || bg[2] == 0 || cg[1] == 0 || cg[2] == 0,
        error("Some parameter has a zero coordinate"));
      F += xi[i][1] * gam[j][1] * Lab(N, ag, bg, B);
      r += xi[i][1] * gam[j][1] * z3ab(N, ag, bg)));
  [F, r];
}

\\  Special case: the Goncharov regulator G(a,b)

\\  The function Gab computes the Goncharov
\\  regulator G(a,b) for a, b in (Z/NZ)^2 such
\\  that the coordinates of a, b, a+b are nonzero.
\\
\\  Input:
\\
\\  * the level N
\\  * the parameters a = [a1, a2] and b = [b1, b2]
\\    satifying the above assumptions
\\  * the precision B (by default B = 20*N)
\\
\\  Output: a vector [F, r], where
\\
\\  * F is a modular form of weight 2 and level Gamma(N),
\\    given as a power series in x = q^(1/N) with
\\    rational coefficients and precision O(x^B)
\\  * r is a rational number
\\
\\  meaning that G(a,b) equals
\\
\\  pi^2 * L'(F, -1) + r * zeta(3)

{
Gab(N, a, b, B = 20*N) =
  my(c);
  a = a%N;
  b = b%N;
  c = (-a-b)%N;
  if(a[1] == 0 || a[2] == 0 || b[1] == 0 || b[2] == 0 || c[1] == 0 || c[2] == 0,
    error("Some parameter has a zero coordinate"));
  [Lab(N, a, b, B), z3ab(N, a, b)];
}

/******************************/
/* FINAL COMPUTATION IN [B23] */
/******************************/

\\ Lalin's cocycle from Section 4
\\
\\ \xi_15 = -20 \xi((0,1), (0,4))

{
xi_15 =
  [[-20, [0, 1], [0, 4]]];
}

\\ Integration path gamma_15 from Section 5

{
gamma_15 =
  [[2, [1, 9; 2, 19]], [-1, [0, -1; 1, 11]], [-1, [0, -1; 1, 4]], [2, [0, -1; 1, 2]]];
}

\\ Final computation in Section 6

\\ The argument B is the precision of the power series
\\ used in the computation

{
final_computation(B = 300) =
  my(Reg_15, F, r, f_15, c);
  
  print("xi_15 = ", xi_15);
  print();
  print("gamma_15 = ", gamma_15);
  print();
  
  Reg_15 = G_reg(15, xi_15, gamma_15, B);
  F = substpol(Reg_15[1], x^15, q);
  r = Reg_15[2];
  
  print("Regulator of xi_15 over gamma_15 = pi^2 * L'(F, -1) + r * zeta(3) with");
  print();
  print("F = ", F);
  print();
  print("r = ", r);
  print();

  \\ Newform f_15 associated to 15a8
  f_15 = 'q * Ser(ellan(ellinit("15a8"), 20), 'q);
  print("f_15 = ", f_15);
  print();
  
  c = lindep([F, f_15]);
  print("F = ", -c[2]/c[1], " * f_15 + ", F + c[2]/c[1] * f_15);
}
