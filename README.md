# K4-of-modular-curves

*Author:* François Brunault

*Date:* May 2023

This repository contains the files companion to the following preprints.

**\[B20\]** F. Brunault, On the $K_4$ group of modular curves, [arXiv:2009.07614](https://arxiv.org/abs/2009.07614)

The file `K4-reg-num.gp` contains PARI/GP code to compute numerically regulator integrals associated to elements in the $K_4$ group of the modular curve $Y_1(N)$. To use it, you should start PARI/GP in the directory containing the file `K4-reg-num.gp` and the data files `DataH1ell` and `DataH1`. Then type the command

```
\r K4-reg-num.gp
```

The beginning of the file `K4-reg-num.gp` explains several examples of use.

**\[B23\]** F. Brunault, On the Mahler measure of $(1+x)(1+y)+z$, [arXiv:2305.02992](https://arxiv.org/abs/2305.02992)

The file `K4-modular-complex.gp` contains a (partial) PARI/GP implementation of the weight $3$ modular complex $\mathcal{C}_N(3)$, introduced in Section 3 of \[B23\]. This program is used in Section 4 of the same paper. The beginning of the file `K4-modular-complex.gp` explains how to reproduce this computation and how the program can be used more generally. To use the program, you should start PARI/GP in the directory containing the file `K4-modular-complex.gp`, and then type the command

```
\r K4-modular-complex.gp
```

The file `K4-reg-Lvalue.gp` contains a PARI/GP program to compute in exact form the Goncharov regulator of the elements $\xi(a,b)$ in the $K_4$ group of the modular curve $Y(N)$ which were introduced in \[B20\]. This program is used in Section 6 of \[B23\]. The beginning of the file `K4-reg-Lvalue.gp` explains how to reproduce this computation and how the program can be used more generally. To use the program, you should start PARI/GP in the directory containing the file `K4-modular-complex.gp`, and then type the command

```
\r K4-reg-Lvalue.gp
```

The SageMath notebook `ModularSymbolGamma15.ipynb` contains computations with modular symbols used in Section 5 of \[B23\].



Shield: [![CC BY 4.0][cc-by-shield]][cc-by]

This work is licensed under a
[Creative Commons Attribution 4.0 International License][cc-by].

[![CC BY 4.0][cc-by-image]][cc-by]

[cc-by]: http://creativecommons.org/licenses/by/4.0/
[cc-by-image]: https://i.creativecommons.org/l/by/4.0/88x31.png
[cc-by-shield]: https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg
