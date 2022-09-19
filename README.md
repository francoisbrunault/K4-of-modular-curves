# K4-of-modular-curves

Author: François Brunault

Date: September 2022

This repository contains the files companion to the preprint

F. Brunault, On the K4 group of modular curves

The file K4.gp contains the PARI/GP code for computing numerically the regulators of certain K_4 classes on the modular curve Y_1(N).

Note: to use these programs, you should start PARI/GP in the directory containing the file "K4.gp" and the data files "DataH1ell" and "DataH1". Then type the command

\r K4.gp

Examples of use:

Section 8:

1) To check numerically Beilinson's conjecture on $L(E,3)$ for the elliptic curve E = 15a1, with precision 40 digits:

checkBeilinson("15a1", 40)

2) To check numerically Beilinson's conjecture on L(E,3) for all elliptic curves E of conductor <= 20, with precision 25 digits:

checkBeilinson([1, 20], 25)

Section 9:

To check numerically Conjecture 9.3 (comparison between the K_4 elements and the Beilinson elements defined using the Eisenstein symbol), for levels 11 <= N <= 28 and precision 40 digits:

checkElements(11, 28, 40)



Shield: [![CC BY 4.0][cc-by-shield]][cc-by]

This work is licensed under a
[Creative Commons Attribution 4.0 International License][cc-by].

[![CC BY 4.0][cc-by-image]][cc-by]

[cc-by]: http://creativecommons.org/licenses/by/4.0/
[cc-by-image]: https://i.creativecommons.org/l/by/4.0/88x31.png
[cc-by-shield]: https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg
