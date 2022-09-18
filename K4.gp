/**************************************/
/* ON THE K_4 GROUP OF MODULAR CURVES */
/**************************************/

/*

Author: François Brunault
Date: July 2022

Note: to use these programs, you should start PARI/GP in the directory containing the file "K4.gp" and the data files "DataH1ell" and "DataH1". Then type the command

\r K4.gp

Examples of use:

Section 8:

1) To check numerically Beilinson's conjecture on L(E,3) for the elliptic curve E = 15a1, with precision 40 digits:

checkBeilinson("15a1", 40)

2) To check numerically Beilinson's conjecture on L(E,3) for all elliptic curves E of conductor <= 20, with precision 25 digits:

checkBeilinson([1, 20], 25)

Section 9:

To check numerically Conjecture 9.3 (comparison between the K_4 elements and the Beilinson elements defined using the Eisenstein symbol), for levels 11 <= N <= 28 and precision 40 digits:

checkElements(11, 28, 40)

*/


\\ Load data files

read("DataH1ell");
read("DataH1");


/***********************/
/* AUXILIARY FUNCTIONS */
/***********************/


\\ Function vsearch
\\
\\ Given an element x and a vector v, returns the smallest i
\\ such that v[i] = x, or returns 0 if x does not belong to v.

{
vsearch(x, v) =
  for(i=1, #v,
    if(v[i] == x,
      return(i)));
  0;
}

\\ Function red
\\
\\ Given a in (Z/NZ)/{±1}, returns the representative
\\ x of a satisfying 0 <= x <= N/2

{
red(a, N) =
  a = a%N;
  min(a, N-a);
}


/***********************************************************/
/* TRIANGULATION OF THE MANIN RELATIONS IN K_2 (SECTION 4) */
/***********************************************************/


/*
Given a,b in Z/NZ, the function Triangulation(N, a, b)
computes a triangulation of the relation
  
  {g_a, g_b} + {g_b, g_c} + {g_c, g_a} = 0

in K_2(Y_1(N)) \otimes Q, where a+b+c = 0.

The output is a vector of vectors [n, x, y, z, t],
meaning the linear combination \sum n {u(x,y,z,t)}_2
in the Bloch group of the function field of Y_1(N).
*/


{
Triangulation_odd(N, a, b) =
  my(coefs = [], xi = [], v, v0, i);
  for(x = 1, N-1,
    v = apply(t -> red(t, N), [0, x, a-x, b+x]);
    v0 = Set(v);
    if(#v0 == 4,
      i = vsearch(v0, xi);
      if(i,
        coefs[i] += permsign(vecsort(v, , 1)),
        xi = concat(xi, [v0]);
        coefs = concat(coefs, permsign(vecsort(v, , 1))))));
  coefs /= N;
  vector(#xi, j, concat(coefs[j], xi[j]));
}

\\ Case N is even

{
Triangulation_even(N, a, b) =
  my(coefs = [], xi = [], v, v0, i);
  xi = [];
  for(x = 1, N-1,
    v = apply(t -> red(t, N), [0, x, a-x, b+x]);
    v0 = Set(v);
    if(#v0 == 4,
      i = vsearch(v0, xi);
      if(i,
        coefs[i] += permsign(vecsort(v, , 1)),
        xi = concat(xi, [v0]);
        coefs = concat(coefs, permsign(vecsort(v, , 1))))));
  coefs /= N;
  \\ If a is even, the sum of the terms \delta(0, a, c+2x, y) vanishes
  if(a % 2 == 1,
    for(x = 0, N/2-1,
      for(y = 0, N/2-1,
        v = apply(t -> red(t, N), [0, a, a+b+2*x, a+b+1+2*y]);
        v0 = Set(v);
        if(#v0 == 4,
          i = vsearch(v0, xi);
          if(i,
            coefs[i] += -permsign(vecsort(v, , 1))/(2*N^2),
            xi = concat(xi, [v0]);
            coefs = concat(coefs, -permsign(vecsort(v, , 1))/(2*N^2)))))));
  \\ If c is even, the sum of the terms \delta(0, c, b+2x, y) vanishes
  if((a+b) % 2 == 1,
    for(x = 0, N/2-1,
      for(y = 0, N/2-1,
        v = apply(t -> red(t, N), [0, a+b, b+2*x, b+1+2*y]);
        v0 = Set(v);
        if(#v0 == 4,
          i = vsearch(v0, xi);
          if(i,
            coefs[i] += -permsign(vecsort(v, , 1))/(2*N^2),
            xi = concat(xi, [v0]);
            coefs = concat(coefs, -permsign(vecsort(v, , 1))/(2*N^2)))))));
  \\ If b is even, the sum of the terms \delta(0, b, a+2x, y) vanishes
  if(b % 2 == 1,
    for(x = 0, N/2-1,
      for(y = 0, N/2-1,
        v = apply(t -> red(t, N), [0, b, a+2*x, a+1+2*y]);
        v0 = Set(v);
        if(#v0 == 4,
          i = vsearch(v0, xi);
          if(i,
            coefs[i] += -permsign(vecsort(v, , 1))/(2*N^2),
            xi = concat(xi, [v0]);
            coefs = concat(coefs, - permsign(vecsort(v, , 1))/(2*N^2)))))));
  vector(#xi, j, concat(coefs[j], xi[j]));
}

{
Triangulation(N, a, b) =
  if(N % 2,
    Triangulation_odd(N, a, b),
    Triangulation_even(N, a, b));
}


/*************************************/
/* ASYMPTOTIC EXPANSIONS (SECTION 7) */
/*************************************/


/*
Let f(y) be a complex-valued function of a real variable y > 0. We assume that f has the following asymptotic expansion when y -> +oo:

f(y) = \sum_j y^j f_j(q_N)

where j in Z, f_j is a power series in q_N = exp(-2 pi y/N),
and the sum over j is finite. We also assume that f(1/y) has
an asymptotic expansion of the same shape when y -> +oo:

f(1/y) = \sum_j y^j g_j(qN).

We represent f by a pair [Foo, F0] where Foo is a vector of
two-component vectors [j, f_j] with f_j a power series in qN,
and F0 is a vector of two-component vectors [j, g_j] with
g_j a power series in qN.
*/


\\ Evaluate an asymptotic expansion
\\
\\ Input: An asymptotic expansion Foo and a real number y0 > 0
\\ Output: Foo(y0)

{
qexp_eval1(F, N, y0) =
  my(q0, j, f, P, Fy0);
  q0 = exp(-2*Pi*y0/N);
  for(i = 1, #F,
    j = F[i][1];
    f = F[i][2];
    P = Pol(f);
    Fy0 += y0^j * subst(P, variable(P), q0));
  Fy0;
}

\\ Evaluate a function
\\
\\ Input: A function f = [Foo, F0] and a real number y0 > 0
\\ Output: f(y0)

{
qexp_eval(F, N, y0) =
  qexp_eval1(F[1], N, y0);
}

\\ Check accuracy of a function
\\
\\ Input: A function f = [Foo, F0] and a real number y0 > 0
\\ Output: Foo(y0) - F0(1/y0)

{
qexp_check(F, N, y0 = 1) =
  my([Foo, F0] = F);
  qexp_eval1(Foo, N, y0) - qexp_eval1(F0, N, 1/y0);
}

\\ Normalise an asymptotic expansion by
\\ collecting the terms with the same exponents j.

{
qexp_norm1(F) =
  my(bool, H = []);
  for(i = 1, #F,
    bool = 0;
    for(k = 1, #H,
      if(F[i][1] == H[k][1],
        H[k][2] += F[i][2];
        bool = 1;
        break()));
    if(!bool,
      H = concat(H, [F[i]])));
  H;
}

\\ Normalise a function (same as above)

{
qexp_norm(F) = 
  [qexp_norm1(F[1]), qexp_norm1(F[2])];
}

\\ Add two functions f = [Foo, F0] and g = [Goo, G0]

{
qexp_add(F, G) =
  my(Foo, F0, Goo, G0, Hoo, H0);
  [Foo, F0] = F;
  [Goo, G0] = G;
  Hoo = concat(Foo, Goo);
  Hoo = qexp_norm1(Hoo);
  H0 = concat(F0, G0);
  H0 = qexp_norm1(H0);
  [Hoo, H0];
}

\\ Linear combination of asymptotic expansions

\\ Input: a vector of scalars [n_1, ..., n_r] and
\\        a vector of functions [F_1, ..., F_r]
\\ Output: the function \sum_i n_i F_i

{
qexp_lin(nvec, Fvec) =
  my(n, Foo, F0, Hoo = [], H0 = []);
  for(i = 1, #Fvec,
    n = nvec[i];
    [Foo, F0] = Fvec[i];
    for(j = 1, #Foo,
      Foo[j][2] *= n);
    Hoo = concat(Hoo, Foo);
    for(j = 1, #F0,
      F0[j][2] *= n);
    H0 = concat(H0, F0));
  Hoo = qexp_norm1(Hoo);
  H0 = qexp_norm1(H0);
  [Hoo, H0];
}

\\ Multiply two functions f = [Foo, F0] and g = [Goo, G0]

{
qexp_mul(F, G) =
  my([Foo, F0] = F, [Goo, G0] = G, Hoo = [], H0 = []);
  for(i = 1, #Foo,
    for(j = 1, #Goo,
      Hoo = concat(Hoo, [[Foo[i][1]+Goo[j][1], Foo[i][2]*Goo[j][2]]])));
  Hoo = qexp_norm1(Hoo);
  for(i = 1, #F0,
    for(j = 1, #G0,
      H0 = concat(H0, [[F0[i][1]+G0[j][1], F0[i][2]*G0[j][2]]])));
  H0 = qexp_norm1(H0);
  [Hoo, H0];
}

\\ Differentiate an asymptotic expansion
\\
\\ Input: an asymptotic expansion Foo
\\ Output: (d/dy)Foo(y)

{
qexp_deriv1(F, N) =
  my(w = -2*Pi/N, j, f, g, G = []);
  for(i = 1, #F,
    j = F[i][1];
    f = F[i][2];
    g = w * variable(f) * deriv(f);
    G = concat(G, [[j, g]]);
    if(j != 0,
      G = concat(G, [[j-1, j*f]])));
  qexp_norm1(G);
}

\\ Differentiate a function f = [Foo, F0]

{
qexp_deriv(F, N) =
  my([Foo, F0] = F, Goo, G0);
  Goo = qexp_deriv1(Foo, N);
  G0 = qexp_deriv1(F0, N);
  for(i = 1, #G0,
    G0[i][1] += 2;
    G0[i][2] = -G0[i][2]);
  [Goo, G0];
}

\\ Integrate an asymptotic expansion Foo = [[j, f_j], ...]

\\ We assume that for negative j, the function f_j is
\\ constant, and is 0 in the case j = -1 (otherwise
\\ we cannot integrate in closed form).

\\ The output g(y) = \sum y^j g_j(y) is normalised by
\\ the condition that the constant term g_0(oo) is zero
\\ (in other words the regularised value of g at oo is 0).

{
qexp_int1(F, N) =
  my(w = N/(2*Pi), j, f, qN, B, P, a0, c, G = []);
  for(i = 1, #F,
    j = F[i][1];
    f = F[i][2];
    qN = variable(f);
    B = serprec(f, qN);
    P = Vec(f, -B); \\ Vector of coefficients a_0, ..., a_{B-1} of f_j
    a0 = P[1];      \\ Constant term of f_j
    \\ First integrate the constant term of f_j
    if(j < 0,
      \\ Case j < 0
      if(f != a0,
        error("The exponents of y should be >= 0"));
      if(j == -1 && a0 != 0,
        error("Cannot integrate 1/y"));
      if(a0 != 0,
        G = concat(G, [[j+1, a0/(j+1) + O(qN^B)]])),
      \\ Case j >= 0
      G = concat(G, [[j+1, a0/(j+1) + O(qN^B)]]));
    \\ Then integrate the other terms
    c = w;
    for(i = 0, j,
      g = -c * vector(B-1, n, P[n+1]/n^(i+1));
      g = concat(0, g);
      G = concat(G, [[j-i, Ser(g, qN)]]);
      c *= w * (j-i)));
  qexp_norm1(G);
}

\\ Integrate a function with given asymptotic expansions at oo and 0.

\\ Input: a function f = [Foo, F0] and a constant C
\\ Output: the asymptotic expansion of the primitive
\\ F(y) = \int f(y) dy whose regularised value at oo
\\ is equal to C.

{
qexp_int(F, N, C = 0) =
  my([Foo, F0] = F, qN, B, H, Goo, G0, C0);
  qN = variable(Foo[1][2]);
  B = serprec(Foo[1][2], qN);
  Goo = qexp_int1(Foo, N);
  Goo = concat(Goo, [[0, C + O(qN^B)]]);
  Goo = qexp_norm1(Goo);
  H = F0;
  for(i = 1, #H,
    H[i][1] -= 2;
    H[i][2] = -H[i][2]);
  G0 = qexp_int1(H, N);
  qN = variable(G0[1][2]);
  B = serprec(G0[1][2], qN);
  C0 = qexp_eval1(Goo, N, 1) - qexp_eval1(G0, N, 1);
  G0 = concat(G0, [[0, C0 + O(qN^B)]]);
  G0 = qexp_norm1(G0);
  [Goo, G0];
}


/**********************************************/
/* GENERALISED MELLIN TRANSFORM (SECTION 7.2) */
/**********************************************/


/*
The generalised Mellin tranform of f : (0, +oo) -> C
is defined as the regularised integral

M_f(s) = \int_0^{oo} f(y) y^s dy/y      (s in C).
*/


\\ Mellin transform of a function
\\
\\ Input: A function f = [Foo, F0] and a complex number s
\\ Output: M_f(s)

{
mellin(F, N, s) =
  my(w = 2*Pi/N, Foo, F0, j, f, B, a0, an, t, b0, bn, Inum);
  [Foo, F0] = F;
  for(i = 1, #Foo,
    j = Foo[i][1];
    f = Foo[i][2];
    if(f != 0,
      B = serprec(f, variable(f));
      a0 = polcoef(f, 0);
      if(a0 != 0 && s != -j,
        Inum -= a0/(s+j));
      for(n = 1, B-1,
        an = polcoef(f, n);
        if(an != 0,
          t = n * w;
          Inum += an * t^(-s-j) * incgam(s+j, t)))));
  for(i = 1, #F0,
    j = F0[i][1];
    f = F0[i][2];
    if(f != 0,
      B = serprec(f, variable(f));
      b0 = polcoef(f, 0);
      if(b0 != 0 && s != j,
        Inum += b0/(s-j));
      for(n = 1, B-1,
        bn = polcoef(f, n);
        if(bn != 0,
          t = n * w;
          Inum += bn * t^(s-j) * incgam(j-s, t)))));
  Inum;
}


/*********************************************/
/* FOURIER EXPANSIONS INVOLVING SIEGEL UNITS */
/*********************************************/


/*
Below are functions computing the asymptotic expansions of
functions like log(g_{a,b}), where g_{a,b} is the Siegel unit.

Notation: qN = exp(-2 pi y/N).
*/


\\ Bernoulli polynomial B_2(x)

{
B2(x) =
  x^2 - x + 1/6;
}

\\ Leading term of g_{a,b} at oo
\\
\\ Input: [a, b] in (Z/NZ)^2
\\ Output: [n, C] such that g_a ~ C * q^n (with n possibly rational)

{
lead_g(ab, N) =
  my([a, b] = ab % N, ord, lead);
  ord = B2(a/N)/2;
  lead = if(a == 0, 1 - exp(2*Pi*I*b/N), 1);
  [ord, lead];
}

\\ Fourier expansion of log |g_{a,b}(iy)| at oo,
\\ where g_{a,b} is the Siegel unit.
\\
\\ Input: A vector ab = [a, b], an integer N and the number of terms B
\\ Output: the expansion with precision O(qN^B)

{
log_g_oo(ab, N, B, qN = 'qN) =
  my([a, b] = ab % N, c, table_cos, f, a1, a2, k, u);
  if(a == 0 && b == 0,
    error("(a, b) must be nonzero mod N"));
  \\ Constant term of the expansion
  if(a == 0,
    c = log(2*sin(Pi*b/N)));
  \\ Table of cos(2*Pi*k/N), 1 <= k <= N-1
  table_cos = vector(N-1, k, cos(2*Pi*k/N));
  f = vector(B-1);
  a1 = if(a == 0, N, a); \\ Starting value for n = a (N)
  a2 = N-a;              \\ Starting value for n = -a (N)
  k = 0;
  for(m = 1, (B-1)\(min(a1, a2)),
    k = (k + b) % N;
    u = if(k == 0, 1/m, table_cos[k]/m);
    forstep(n = a1, (B-1)\m, N,
      f[m*n] += u);
    forstep(n = a2, (B-1)\m, N,
      f[m*n] += u));
  f = concat(c, -f);
  [[1, -Pi*B2(a/N) + O(qN^B)], [0, Ser(f, qN)]];
}

\\ Fourier expansions of log |g_{a,b}|
\\
\\ Input: A vector ab = [a, b], an integer N and the number of terms B
\\ Output: The function log |g_{a,b}| with precision O(qN^B)

{
log_g(ab, N, B, qN = 'qN) =
  my([a, b] = ab);
  [log_g_oo(ab, N, B, qN), log_g_oo([b, -a], N, B, qN)];
}

\\ Fourier expansion of (d/dy) log |g_{a,b}(iy)| at oo
\\
\\ Input: A vector ab = [a, b], an integer N and the number of terms B
\\ Output: the expansion with precision O(qN^B)

{
dlog_g_oo(ab, N, B, qN = 'qN) =
  my([a, b] = ab % N, c, w, table_cos, f, a1, a2, k, u);
  if(a == 0 && b == 0,
    error("(a, b) must be nonzero mod N"));
  \\ Constant term of the expansion
  c = -Pi * B2(a/N);
  \\ Table of cos(2*Pi*k/N), 1 <= k <= N-1
  w = 2 * Pi / N;
  table_cos = vector(N-1, k, cos(k*w));
  f = vector(B-1);
  a1 = if(a == 0, N, a); \\ Starting value for n = a (N)
  a2 = N-a;              \\ Starting value for n = -a (N)
  k = 0;
  for(m = 1, (B-1)\(min(a1, a2)),
    k = (k + b) % N;
    u = if(k == 0, 1, table_cos[k]);
    forstep(n = a1, (B-1)\m, N,
      f[m*n] += u * n);
    forstep(n = a2, (B-1)\m, N,
      f[m*n] += u * n));
  f = concat(c, w * f);
  [[0, Ser(f, qN)]];
}

\\ Fourier expansions of dlog |g_{a,b}|
\\
\\ Input: A vector ab = [a, b], an integer N and the number of terms B
\\ Output: The function (d/dy) log |g_{a,b}(iy)| with precision O(qN^B)

{
dlog_g(ab, N, B, qN = 'qN) =
  my([a, b] = ab, Foo, F0);
  Foo = dlog_g_oo(ab, N, B, qN);
  F0 = dlog_g_oo([b, -a], N, B, qN);
  F0[1][1] = 2;
  F0[1][2] = -F0[1][2];
  [Foo, F0];
}

\\ Fourier expansion of (d/dy) arg g_{a,b}(iy) at oo
\\
\\ Input: A vector ab = [a, b], an integer N and the number of terms B
\\ Output: the expansion with precision O(qN^B)

{
darg_g_oo(ab, N, B, qN = 'qN) =
  my([a, b] = ab % N, w, table_sin, f, a1, a2, k, u);
  if(a == 0 && b == 0,
    error("(a, b) must be nonzero mod N"));
  \\ Table of sin(2*Pi*k/N), 1 <= k <= N-1
  w = 2 * Pi / N;
  table_sin = vector(N-1, k, sin(k*w));
  f = vector(B-1);
  a1 = if(a == 0, N, a); \\ Starting value for n = a (N)
  a2 = N-a;              \\ Starting value for n = -a (N)
  k = 0;
  for(m = 1, (B-1)\(min(a1, a2)),
    k = (k + b) % N;
    u = if(k == 0, 0, table_sin[k]);
    forstep(n = a1, (B-1)\m, N,
      f[m*n] += u * n);
    forstep(n = a2, (B-1)\m, N,
      f[m*n] -= u * n));
  f = concat(0, w * f);
  [[0, Ser(f, qN)]];
}

\\ Fourier expansions of darg g_{a,b}
\\
\\ Input: A vector ab = [a, b], an integer N and the number of terms B
\\ Output: The function (d/dy) arg g_{a,b}(iy) with precision O(qN^B)

{
darg_g(ab, N, B, qN = 'qN) =
  my([a, b] = ab, Foo, F0);
  Foo = darg_g_oo(ab, N, B, qN);
  F0 = darg_g_oo([b, -a], N, B, qN);
  F0[1][1] = 2;
  F0[1][2] = -F0[1][2];
  [Foo, F0];
}


/**********************************************/
/* FOURIER EXPANSIONS INVOLVING u(a, b, c, d) */
/**********************************************/


\\ We represent a divisor z on (Z/NZ)^2 as a vector of
\\ vectors [n, [a, b]], meaning z = \sum n*[(a,b)].
\\ The associated modular unit is g_z = \prod g_{a,b}^n

\\ Fourier expansions of log |g_z|
\\
\\ Input: A divisor z on (Z/NZ)^2, an integer N and the precision B
\\ Output: The function log |g_z| with precision O(qN^B)

{
log_g_div(z, N, B, qN = 'qN) =
  my(n, ab, foo, f0, Foo, F0);
  Foo = [[1, O(qN^B)], [0, O(qN^B)]];
  F0 = [[1, O(qN^B)], [0, O(qN^B)]];
  for(i = 1, #z,
    [n, ab] = z[i];
    [foo, f0] = log_g(ab, N, B, qN);
    Foo[1][2] += n * foo[1][2];
    Foo[2][2] += n * foo[2][2];
    F0[1][2] += n * f0[1][2];
    F0[2][2] += n * f0[2][2]);
  [Foo, F0];
}

\\ Fourier expansions of dlog |g_z|
\\
\\ Input: A divisor z on (Z/NZ)^2, an integer N and the precision B
\\ Output: The function (d/dy) log |g_z(iy)| with precision O(qN^B)

{
dlog_g_div(z, N, B, qN = 'qN) =
  my(n, ab, foo, f0, Foo, F0);
  Foo = [[0, O(qN^B)]];
  F0 = [[2, O(qN^B)]];
  for(i = 1, #z,
    [n, ab] = z[i];
    [foo, f0] = dlog_g(ab, N, B, qN);
    Foo[1][2] += n * foo[1][2];
    F0[1][2] += n * f0[1][2]);
  [Foo, F0];
}

\\ Fourier expansions of darg g_z
\\
\\ Input: A divisor z on (Z/NZ)^2, an integer N and the precision B
\\ Output: The function (d/dy) arg g_z(iy) with precision O(qN^B)

{
darg_g_div(z, N, B, qN = 'qN) =
  my(n, ab, foo, f0, Foo, F0);
  Foo = [[0, O(qN^B)]];
  F0 = [[2, O(qN^B)]];
  for(i = 1, #z,
    [n, ab] = z[i];
    [foo, f0] = darg_g(ab, N, B, qN);
    Foo[1][2] += n * foo[1][2];
    F0[1][2] += n * f0[1][2]);
  [Foo, F0];
}

\\ Fourier expansions of log |u(a, b, c, d)|
\\
\\ Input: a, b, c, d in (Z/NZ)^2/{±1} distinct, integers N and B
\\ Output: the function log |u(a, b, c, d)| with precision O(qN^B)

{
log_u(a, b, c, d, N, B, qN = 'qN) =
  my(z);
  z = [[1, c+a], [1, c-a], [1, d+b], [1, d-b], [-1, c+b], [-1, c-b], [-1, d+a], [-1, d-a]];
  log_g_div(z, N, B, qN);
}

\\ Fourier expansions of dlog |u(a, b, c, d)|
\\
\\ Input: a, b, c, d in (Z/NZ)^2/{±1} distinct, integers N and B
\\ Output: the function (d/dy) log |u(a, b, c, d)(iy)|
\\         with precision O(qN^B)

{
dlog_u(a, b, c, d, N, B, qN = 'qN) =
  my(z);
  z = [[1, c+a], [1, c-a], [1, d+b], [1, d-b], [-1, c+b], [-1, c-b], [-1, d+a], [-1, d-a]];
  dlog_g_div(z, N, B, qN);
}

\\ Fourier expansions of darg u(a, b, c, d)
\\
\\ Input: a, b, c, d in (Z/NZ)^2/{±1} distinct, integers N and B
\\ Output: the function (d/dy) arg u(a, b, c, d)(iy)
\\         with precision O(qN^B)

{
darg_u(a, b, c, d, N, B, qN = 'qN) =
  my(z);
  z = [[1, c+a], [1, c-a], [1, d+b], [1, d-b], [-1, c+b], [-1, c-b], [-1, d+a], [-1, d-a]];
  darg_g_div(z, N, B, qN);
}

\\ Leading term at oo of the infinite product
\\ gamma_a(tau) with a in Z^2

{
lead_gamma(a, N) =
  my([a1, a2] = a, m, r, ord, lead);
  [m, r] = divrem(a1, N);
  ord = -m*r - N*m*(m-1)/2;
  lead = (-1)^m * exp(-2*Pi*I*a2*m/N);
  if(r == 0, lead *= 1-exp(2*Pi*I*a2/N));
  [ord, lead];
}

\\ Leading term of u(a, b, c, d) at oo
\\
\\ Input: a, b, c, d in (Z/NZ)^2
\\ Output: [n, C] such that u(a, b, c, d) ~ C * q^n (n possibly rational)

{
lead_u(a, b, c, d, N) =
  my(leads1, leads2, ord, lead);
  leads1 = apply(x -> lead_gamma(x, N), [c+a, c-a, d+b, d-b]);
  leads2 = apply(x -> lead_gamma(x, N), [c+b, c-b, d+a, d-a]);
  ord = sum(i = 1, 4, leads1[i][1] - leads2[i][1]);
  lead = prod(i = 1, 4, leads1[i][2] / leads2[i][2]);
  [ord, lead];
}

\\ The Bloch-Wigner dilogarithm

{
D(z) =
  polylog(2, z, 2);
}

\\ Fourier expansions of D(u(a, b, c, d))
\\
\\ Strategy: compute the derivative, the value at oo and integrate.

\\ Input: a, b, c, d in (Z/NZ)^2/{±1} distinct, integers N and B
\\ Output: the function D(u(a, b, c, d)) with precision O(qN^B)

{
Du(a, b, c, d, N, B, qN = 'qN) =
  my(F1, F2, F, ord, lead, C);
  F1 = qexp_mul(log_u(a, b, c, d, N, B, qN), darg_u(a, c, b, d, N, B, qN));
  F2 = qexp_mul(log_u(a, c, b, d, N, B, qN), darg_u(a, b, c, d, N, B, qN));
  F = qexp_lin([1, -1], [F1, F2]);
  [ord, lead] = lead_u(a, b, c, d, N);
  C = if(ord == 0, D(lead), 0);
  qexp_int(F, N, C);
}


/**************************/
/* RESIDUES OF \xi_1(a,b) */
/**************************/


/*
We compute here numerically the residues of
the elements \xi_1(a, b) at the cusps of X_1(N).

A set of representatives of the Galois orbits of the cusps
of X_1(N) is given by the cusps 1/v with 0 <= v <= N/2.

Among them, the real cusps are: v = 0, v = N/2 (if N even)
and the integers 0 < v < N/2 such that gcd(v, N) \in {1, 2}.

So the cusps which are not real are given by the integers
0 < v < N/2 such that gcd(v, N) >= 3. In this case, the
residue field is the cyclotomic field Q(zeta_d) with
d = gcd(v, N).
*/


\\ Function lead_gamma_exact
\\
\\ Input: a in (Z/NZ)^2
\\ Output: Leading term at oo of the infinite product
\\ gamma_a(tau) with a in Z^2, where the leading
\\ coefficient is given as an element of Q(zeta_N)

{
lead_gamma_exact(a, N) =
  my([a1, a2] = a, m, r, ord, lead, zN = Mod(t, polcyclo(N, t)));
  [m, r] = divrem(a1, N);
  ord = -m*r - N*m*(m-1)/2;
  lead = (-zN^(-a2))^m;
  if(r == 0, lead *= 1-zN^a2);
  [ord, lead];
}

\\ Function lead_u_exact
\\
\\ Input: a, b, c, d in (Z/NZ)^2
\\ Output: [n, C] such that u(a, b, c, d) ~ C * q^n,
\\         where C is an element of Q(zeta_N) and n rational.

{
lead_u_exact(a, b, c, d, N) =
  my(leads1, leads2, ord, lead);
  leads1 = apply(x -> lead_gamma_exact(x, N), [c+a, c-a, d+b, d-b]);
  leads2 = apply(x -> lead_gamma_exact(x, N), [c+b, c-b, d+a, d-a]);
  ord = sum(i = 1, 4, leads1[i][1] - leads2[i][1]);
  lead = prod(i = 1, 4, leads1[i][2] / leads2[i][2]);
  [ord, lead];
}

\\ Function lift_ZNZ_star
\\
\\ Input: integers N, m, a with m | N and (a, m) = 1.
\\ Output: integer b such that b = a (m) and (b, N) = 1.

{
lift_ZNZ_star(N, m, a) =
  my(b = a);
  if(N % m != 0,
    error("m must divide N"));
  if(gcd(a, m) != 1,
    error("a must be coprime to m"));
  for(k = 1, N/m,
    if(gcd(b, N) == 1,
      return(b),
      b += m));
}

\\ Residue of the symbol {u(a, b, c, d)}_2 \otimes g_e
\\ at the cusp 1/v0, as floating-point number.

{
Res_cusp(N, a, b, c, d, e, v0) =
  my(v = v0 % N, m, w, g, lead, ord, r, zN = exp(2*Pi*I/N), Res_v);
  v = min(v, N-v);
  m = gcd(v, N);
  if(v == 0 || v == N/2 || m <= 2,
    return([]));
  \\ The residue field of the cusp is Q(zeta_m)
  w = N/m;       \\ Width of the cusp
  g = [1, 0; v, 1];
  ord = lead_g(e*g, N)[1] * w;
  if(ord == 0,
    return(vector(eulerphi(m)/2)));
  lead = lead_u_exact(a*g, b*g, c*g, d*g, N);
  if(lead[1] != 0,
    return(vector(eulerphi(m)/2)));
  lead = lift(lead[2]);
  Res_v = [];
  for(i = 1, ceil(m/2)-1,
    if(gcd(i, m) == 1,
      r = lift_ZNZ_star(N, m, i);
      Res_v = concat(Res_v, ord * D(subst(lead, variable(lead), zN^r)))));
  Res_v;
}

\\ The residues of \xi_1(a,b) at the non-real
\\ cusps of X_1(N), as floating-point numbers

{
residues(N, a, b) =
  my(T = Triangulation(N, a, b), Res = [], Res_v, m, x, y, z, w);
  \\ Loop over the Galois orbits of non-real cusps of X_1(N)
  for(v = 3, ceil(N/2)-1,
    m = gcd(v, N);
    if(m >= 3,
      Res_v = vector(eulerphi(m)/2);
      for(i = 1, #T,
        n = T[i][1];
        [x, y, z, w] = apply(t -> [0, t], T[i][2..5]);
        Res_v += n * (Res_cusp(N, x, y, z, w, [0, b], v) - Res_cusp(N, x, y, z, w, [0, a], v)));
      Res = concat(Res, [[v, Res_v]])));
  Res;
}

\\ Given an integer N and a, b in Z/NZ, the function
\\ check_residues computes the residues of the class
\\ \xi_1(a,b) at the cusps of X_1(N). It returns 1 if
\\ the residues are all numerically equal to 0 (that is,
\\ the class \xi_1(a,b) should extend to X_1(N)),
\\ and 0 otherwise.

{
check_residues(N, a, b, verb) =
  my(prec, R, Rv);
  prec = default(realbitprecision);
  R = residues(N, a, b);
  for(i = 1, #R,
    Rv = R[i][2];
    for(j = 1, #Rv,
      if(abs(Rv[j]) > 1.>>(prec\2),
        if(verb,
          print("Non-zero residue at the cusp 1/", R[i][1]));
        return(0))));
  if(verb,
    print("Residues are numerically zero"));
  1;
}


/***********************************************************/
/* NUMERICAL COMPUTATION OF THE REGULATOR r_3(2) ON Y_1(N) */
/***********************************************************/


\\ Fourier expansion of Goncharov's regulator r_3(2)
\\ for the symbols {u(x,y,z,w)}_2 \otimes (g_b/g_a) with
\\ x, y, z, w in (Z/NZ)^2/{±1} and a, b in (Z/NZ)^2-{0}.

{
r32(x, y, z, w, a, b, N, B, qN = 'qN) =
  my(DDu, DAg, Lg, Lu, DLu, L1u, DL1u, F1, F2, F3);
  DDu = Du(x, y, z, w, N, B, qN);
  DAg = qexp_lin([1, -1], [darg_g(b, N, B, qN), darg_g(a, N, B, qN)]);
  Lg = qexp_lin([1, -1], [log_g(b, N, B, qN), log_g(a, N, B, qN)]);
  Lu = log_u(x, y, z, w, N, B, qN);
  DLu = dlog_u(x, y, z, w, N, B, qN);
  L1u = log_u(x, z, y, w, N, B, qN);
  DL1u = dlog_u(x, z, y, w, N, B, qN);
  F1 = qexp_mul(DDu, DAg);
  F2 = qexp_mul(Lg, qexp_mul(L1u, DLu));
  F3 = qexp_mul(Lg, qexp_mul(Lu, DL1u));
  qexp_lin([-1, 1/3, -1/3], [F1, F2, F3]);
}

\\ Integral of Goncharov's regulator r_3(2)(xi_1(a,b))
\\ along a modular symbol gamma.
\\
\\ Input: an integer N, elements a, b in Z/NZ, and
\\        a modular symbol gamma = \sum_g n_g {g.0, g.oo}.
\\        given as a vector of vectors [n_g, a, b, c, d]
\\        with g = [a, b; c, d].
\\ Output: the integral of r_3(2)(xi_1(a,b)) over gamma.

{
r32_int(N, a, b, gam, B) =
  my(T = Triangulation(N, a, b), F, x, y, z, w, n, s, t, u, v, g);
  F = [[[0, O('qN^B)]], [[0, O('qN^B)]]];
  for(i = 1, #T,
    m = T[i][1];
    [x, y, z, w] = apply(X -> [0, X], T[i][2..5]);
    for(j = 1, #gam,
      [n, s, t, u, v] = gam[j];
      g = [s, t; u, v];
      F = qexp_lin([1, m*n], [F, r32(x*g, y*g, z*g, w*g, [0, a]*g, [0, b]*g, N, B)])));
  mellin(F, N, 1);
}


/*******************************************************/
/* NUMERICAL CHECK OF BEILINSON'S CONJECTURE ON L(E,3) */
/*******************************************************/


/*
We check numerically Beilinson's conjecture on L(E,3)
using the K_4 elements constructed in Section 6. More
precisely, for an elliptic curve E of conductor N, we
integrate cocycles xi_1(a,b) with a, b in Z/NZ along
a 1-cycle gamma_E in the Hecke eigenspace attached to E.
The cycle gamma_E is precomputed using Magma and stored
in the file DataH1ell. This file covers all elliptic
curves of conductor up to 100.
*/


\\ Given an elliptic curve E of conductor N, the
\\ function checkBeilinson first finds a cocycle
\\ \xi_1(a,b) on Y_1(N) whose residues at the
\\ cusps are numerically zero. Then it computes
\\ the regulator integral Reg attached to \xi_1(a,b)
\\ along the cycle gamma_E to precision prec (40
\\ digits by default). It searches for a rational
\\ approximation r of the ratio
\\
\\    Reg / (Pi^2 / N * L'(E, -1))
\\
\\ It returns [[E, [a, b], r, eps]] where eps is
\\ the error in the approximation of the above ratio.
\\ If no numerical relation with L(E, 3) has been
\\ found, the function returns [[E, "?"]].
\\
\\ The function checkBeilinson allows as first
\\ argument either a Cremona label, or an
\\ elliptic curve as given by ellinit, or a vector
\\ [N1, N2]. In the latter case all elliptic curves
\\ of conductor between N1 and N2 are tested, and
\\ the function returns a vector of 4-tuples as above.

{
checkBeilinson(curves, prec = 40, verb = 1) =
  my(list_curves = [], label, E, isogeny_class, N1, N2, N, gammaE, L, R, r, r_lin, r_rat, list_ratios = []);
  if(type(curves) == "t_STR", \\ Cremona label
    label = curves;
    E = ellinit(label));
  if(type(curves) == "t_VEC" && #curves > 2,
    \\ Elliptic curve in PARI/GP format
    label = ellidentify(curves)[1][1];
    E = curves);
  if(label != 0,
    isogeny_class = ellconvertname(label)[1..2];
    for(i = 1, #Edata,
      if(ellconvertname(Edata[i])[1..2] == isogeny_class,
        list_curves = [[label, E, gammaEdata[i]]];
        break()));
    if(list_curves == [],
      error("Elliptic curve data not available")),
    \\ Case curves = [N1, N2] is a conductor range
    [N1, N2] = curves;
    for(i = 1, #Edata,
      label = Edata[i];
      N = ellconvertname(label)[1];
      if(N > N2,
        break());
      if(N >= N1,
        E = ellinit(label);
        list_curves = concat(list_curves, [[label, E, gammaEdata[i]]]))));
  for(i = 1, #list_curves,
    [label, E, gammaE] = list_curves[i];
    if(verb,
      print();
      print("E = ", label);
      print());
    N = ellconvertname(label)[1];
    if(verb,
      print("Checking residues..."));
    for(a = 1, N\2,
      for(b = max(a+1, 3), N\2,
        if(verb,
          print();
          print("[a, b] = ", [a, b]));
        if(!check_residues(N, a, b, verb),
          next());
        if(verb,
          print("Computing the regulator to ", prec, " digits..."));
        localprec(prec+10);
        L = Pi^2 / N * lfun(E, -1, 1);
        R = r32_int(N, a, b, gammaE, round(prec/12*5*N));
        r = R/L;
        r_lin = lindep([r, 1], prec\2);
        if(vecmax(abs(r_lin)) > 10^(prec\4),
          if(verb,
            print("Warning: Regulator numerically unrelated to L(E,3)"));
          next());
        if(r_lin[2] == 0,
          if(verb,
            print("Regulator is numerically zero"));
          next());
        r_rat = -r_lin[2]/r_lin[1];
        if(verb,
          print();
          print("Non-zero regulator");
          print("r = ", r_rat, "    ", abs(r-r_rat)));
        list_ratios = concat(list_ratios, [[label, [a, b], r_rat, abs(r-r_rat)]]);
        next(3)));
    if(verb,
      print("Warning: no numerical relation found"));
    list_ratios = concat(list_ratios, [[label, "?"]]));
  list_ratios;
}


/******************************************/
/* COMPARISON WITH THE BEILINSON ELEMENTS */
/******************************************/


\\ EisG(k, N, a, b, B) gives the Eisenstein series
\\ G^(k,N)_{a, b} on Gamma_1(N^2) up to precision
\\ O(q^B) in the variable v (by default v = x).

{
EisG(k, N, a, b, B, v = 'x) =
  my(a0, b0, C0, C, m, n);
  if(k < 1, error("The weight must be >= 1"));
  a = a%N;
  b = b%N;
  \\if(k==2 && a==0, return(0)); \\ Removed to include quasi-modular G^(2)'s
  C0 = 0;
  if(k == 1,
    if(a == 0 && b != 0, C0 = 1/2 - b/N);
    if(a != 0 && b == 0, C0 = 1/2 - a/N));
  if(k >= 2,
    if(b == 0, C0 = -N^(k-1)*subst(bernpol(k), x, a/N)/k));
  C = vector(B-1);
  if(a == 0, a0 = N, a0 = a);
  if(b == 0, b0 = N, b0 = b);
  for(i = 0, ceil((B/b0-a0)/N)-1,
    m = a0+i*N;
    for(j = 0, ceil((B/m-b0)/N)-1,
      n = b0+j*N;
      C[m*n] += m^(k-1)));
  for(i = 1, ceil((B/(N-b)+a)/N)-1,
    m = i*N-a;
    for(j = 1, ceil((B/m+b)/N)-1,
      n = j*N-b;
      C[m*n] += (-1)^k*m^(k-1)));
  C0 + sum(i = 1, B-1, C[i]*v^i) + O(v^B);
}

\\ EisH(k, N, a, b, B) gives the Eisenstein series
\\ H^(k,N)_{a, b} on Gamma_1(N^2) up to precision
\\ O(q^B) in the variable v (by default v = x).

{
EisH(k, N, a, b, B, v = 'x) =
  my(zN = exp(2*Pi*I/N), a0, b0, C0, C, m, n);
  if(k < 1, error("The weight must be >= 1"));
  a = a%N;
  b = b%N;
  \\if(k==2 && a==0, return(0)); \\ Removed to include quasi-modular H^(2)'s
  C0 = 0;
  if(k == 1,
    if(a == 0 && b != 0, C0 = -1/2*(1+zN^b)/(1-zN^b));
    if(a != 0 && b == 0, C0 = -1/2*(1+zN^a)/(1-zN^a));
    if(a != 0 && b != 0, C0 = -1/2*((1+zN^a)/(1-zN^a)+(1+zN^b)/(1-zN^b))));
  if(k >= 2,
    for(y = 0, N-1,
      C0 += -N^(k-1) * zN^((-y*b)%N) * subst(bernpol(k), 'x, y/N)/k));
  C = vector(B-1);
  for(m = 1, B-1,
    for(n = 1, floor((B-1)/m),
      C[m*n] += (zN^((-a*m-b*n)%N) + (-1)^k * zN^((a*m+b*n)%N)) * n^(k-1)));
  C0 + sum(i = 1, B-1, C[i]*v^i) + O(v^B);
}

\\ Integral of the Eisenstein symbol Eis^{0,0,1}((0,a),(0,b))
\\ along a cycle gamma

{
int_Eis001(N, a, b, gam, B) =
  my(F, G, n, c, d, a1, b1, a2, b2, a0, b0, I1, I2);
  for(i = 1, #gam,
    n = gam[i][1];
    [c, d] = gam[i][4..5];
    a1 = (a*c)%N;
    b1 = (a*d)%N;
    a2 = (b*c)%N;
    b2 = (b*d)%N;
    F += n * (EisG(1, N, b1, -a2, N*B) * EisG(1, N, b2, a1, N*B) + EisG(1, N, b1, a2, N*B) * EisG(1, N, b2, -a1, N*B));
    G += n * (EisH(1, N, b1, -a2, B) * EisH(1, N, b2, a1, B) + EisH(1, N, b1, a2, B) * EisH(1, N, b2, -a1, B)));
  F = substpol(F, 'x^N, 'x);
  G = -G/N;
  a0 = polcoef(F, 0);
  b0 = polcoef(G, 0);
  I1 = 0;
  for(n = 1, B-1,
    I1 += polcoef(F, n) * incgam(-1, 2*Pi*n/sqrt(N)) * (2*Pi*n));
  I2 = 0;
  for(n = 1, B-1,
    I2 += polcoef(G, n) * incgam(3, 2*Pi*n/sqrt(N)) / (2*Pi*n)^3);
  (9*Pi / N^3) * (I1 + N^2*I2 + a0 - b0/3);
}
  
{
checkElements(N1, N2, prec = 20, verb = 1) =
  my(H1_X1N, gam, Reg, Eis, B);
  localprec(prec+10);
  for(N = N1, N2,
    print();
    print("N = ", N);
    if(N > #gammaNdata,
      error("Data for this level not available"));
    H1_X1N = gammaNdata[N];
    B = round(prec/12*5*N);
    for(i = 1, #H1_X1N,
      if(verb,
        print();
        print("Cycle #", i));
      gam = H1_X1N[i];
      for(a = 1, N\2,
        for(b = a, N\2,
          Reg = real(r32_int(N, a, b, gam, B));
          Eis = real(int_Eis001(N, a, b, gam, B));
          if(abs(Reg - (N^2/6 * Eis)) > 10^(-prec),
            print("[a, b] = ", [a, b], "    ", Reg - (N^2/6 * Eis));
            print("Regulators are not proportional!"),
            if(verb,
              print("[a, b] = ", [a, b], "    ", Reg - (N^2/6 * Eis))))))));
}
