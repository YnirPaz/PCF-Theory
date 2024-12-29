# PCF-Theory

It was long known that $\text{ZFC}$ decides almost nothing about the power operation on cardinals, $\kappa \mapsto 2 ^ \kappa$, for regular cardinals $\kappa$.
For example even assuming $2 ^ {\aleph_4} = \aleph_5$, so the power function is as small as it can be below $\aleph_5$, we still have that $2 ^ {\aleph_5}$ can be arbitrarily large.
This idea is formalized with Easton's theorem, which proves the only constraints of the power operation on regular cardinals are a few "obvious" ones, such as monotonicity.

It was thought the situation was similar for singular cardinals, until in 1974 Silver showed that if $2 ^ \kappa = \kappa^+$ for every $\kappa < \aleph_ {\omega_1}$, then $2 ^ {\aleph_ {\omega_1}} = \aleph_ {\omega_1 + 1}$. That is, the generalized continuum hypothesis can't fail for the first time at $\aleph_ {\omega_1}$ (or more generally at any singular cardinal with uncountable cofinality).
This was the first indication that a unifying, Easton-like theorem may not exist for singular cardinals, and soon many set-theorists took inspiration and started working on the problem of understanding powers of singular cardinals.

One of the natural ways for the power function to be small below a cardinal $\kappa$ is for powers of cardinals below it to stay below it. That is, for every $\lambda < \kappa$, we also have $2 ^ \lambda < \kappa$. Such a $\kappa$ is called a strong limit cardinal. In 1975 Glavin and Hajnal bounded the value of $2 ^ {\aleph_{\omega_1}}$, assuming $\aleph_{\omega_1}$ is a strong limit cardinal. Much like Silver's theorem this result was the first of its kind, and is one of the main inspirations for PCF theory.

In 1978 Shelah introduced Possible Cofinality Theory (PCF theory), which he used to show that $\aleph_{\omega + 1}$ is not a Jónsson cardinal, an open problem at the time. PCF theory has since found applications in many areas around set theory, including model theory, infinitary logic and general topology, but in particular it has hugely improved our understanding of cardinal arithmetic. Its most famous consequence is the following surprising result:

```math
  \text{If } \aleph_\omega \text{ is a strong limit cardinal, then } 2 ^ {\aleph_ \omega} < \aleph_ {\omega_4}.
```

Whether the $4$ in $\aleph_ {\omega_4}$ is an artifact of the proof or the best possible bound is a major open problem. In the language of PCF theory, this is the question of whether (in certain sets of cardinals $A$) the known bound $|\text{pcf}(A)| < |A|^{+4}$ is tight, or if $|A|^{+4}$ can be reduced. Currently it is not even known if $|\text{pcf}(A)| \ne |A|$ is possible.

This project aims to formalize PCF theory in lean, following article 14, "Cardinal Arithmetic", in the "Handbook of Set Theory".
This article is also a great resource for anyone who wants to learn more about this topic, starting with the very basics.

## Goals

The long-term goal of the project is to formalize enough PCF theory to prove Shelah's theorem:

$$
  \text{If } \aleph_\omega \text{ is a strong limit cardinal, then } 2 ^ {\aleph_ \omega} < \aleph_ {\omega_4}.
$$

The current short-term goal is prove the representation theorem for successors of singular cardinals (theorem 2.23), and use it to construct a Jónsson algebra on $\aleph_ {\omega + 1}$.

## Tasks

As the project is just starting and the basic notions of PCF theory are not defined, there aren't many disjoint tasks to work on yet.
Once the foundations of the project solidify there will hopefully be many independent TODOs and isolated sorrys.

- Prove the countable case of `exists_isClubGuessing_of_cof_uncountable`. This is exercise 2.18.2 in the Handbook and there is a hint that describes the variation on the uncountable case construction.

## Structure

**Background/** contains files with theorems not specific to PCF theory.

**ClubGuessing.lean** proves the basic club guessing principles needed for PCF theory. These are theorem 2.17 and the following exercise in the Handbook.