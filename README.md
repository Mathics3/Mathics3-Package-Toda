# Unstable homotopy groups of spheres

This repository contains Mathematica programs you can download that know many results about the unstable homotopy groups of spheres up to the 19-stem. Most of the information is taken from Toda's book *"Composition methods in homotopy groups of spheres"*; a few additional facts are proved in an accompanying note or quoted from elsewhere. The program does not do any serious calculations for itself; it is merely a convenient way of organizing and accessing results obtained by traditional methods. One can also do some automated consistency checking to detect any errors. I have tried to use a fairly general framework so that other computations in unstable homotopy can be included later if people are interested.


This program is not really finished, but I (Neil P Strickland) think it is already useful, and I have moved on to other things, so I have decided to release it.

Here are some examples of things one can type, and the program's response:

### Example 1
```mathematica
SpherePi[14,2]
```
$$\mathbb{Z}_2\eta_5^\circ\varepsilon_6 \oplus \mathbb{Z}_2\mu_5 \oplus \mathbb{Z}_2\nu_5^\circ\nu_8^\circ\nu_{11}$$

### Example 2
```mathematica
HomotopySet[Sphere[7],Sphere[4]]
```
$$\mathbb{Z}\nu_4 \oplus \mathbb{Z}_4\nu'$$

### Example 3
```mathematica
GroupType[SpherePi[19,10]]
```
$$\mathbb{Z}_2 \oplus \mathbb{Z}_2 \oplus \mathbb{Z}_2 \oplus \mathbb{Z}$$

### Example 4
```mathematica
ShowMap[Hopf,8,4]
```
| $\pi_8^4$ | $\to$ | $\pi_8^7$ |
| :--- | :---: | :--- |
| $\mathbb{Z}_2\nu_4^\circ\eta_7 \oplus \mathbb{Z}_2(\Sigma\nu')^\circ\eta_7$ | | $\mathbb{Z}_2\eta_7$ |
| $\nu_4^\circ\eta_7$ | $\to$ | $\eta_7$ |
| $(\Sigma\nu')^\circ\eta_7$ | $\to$ | $0$ |

### Example 5
```mathematica
ShowMap[Sigma,To[sigmaprime]]
```
| $\pi_{13}^6$ | $\to$ | $\pi_{14}^7$ |
| :--- | :---: | :--- |
| $\mathbb{Z}_4\sigma''$ | | $\mathbb{Z}_8\sigma'$ |
| $\sigma''$ | $\to$ | $2\sigma'$ |

### Example 6
```mathematica
Explain[o[nuprime,nu[7]]]
```
$$\nu'^\circ\nu_7 \to 0$$
> *This takes place in the trivial group $\pi_{10}S^3$ — see Toda's Proposition 5.15*


## Using

```console
$ git clone https://github.com/Mathics3/Mathics3-Packages-Toda toda
$ cd toda
$ mathics3
<<Toda.m
```

## Files

Here are the files:
* [Toda.pdf](toda.pdf) - more detailed documentation
* [Toda.m](Toda.m) - the core of the program
* [TeXToMath.m](TeXToMath.m) - used by Toda.m to convert help messages from LaTeX to Mathematica encoding. (This is rather crude, and will only handle a limited range of LaTeX constructs.)
* [LambdaAlgebra.m](LambdaAlgebra.m) - definitions related to the lambda algebra, including lambda algebra representatives for some of Toda's generators. This program can calculate the cohomology of the lambda algebra, but it uses a very naive and inefficient algorithm, and takes a ridiculous amount of space to represent the result.
* [TodaChecks.m](TodaChecks.m) - some auxiliary functions for checking the completeness and consistency of the results encoded in Toda.m. (There are currently numerous failures of completeness, but none of consistency.)
* [LambdaData.m](LambdaData.m) - 10MB of data on bases for the lambda algebra that put the differential in canonical form. You probably do not want or need to download this file.


## See also

[https://strickland1.org/toda/](https://strickland1.org/toda/)
