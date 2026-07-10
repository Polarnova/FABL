import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter01.ProbabilityDensitiesAndConvolution

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Section 1.5" =>

# 1.5. Probability densities and convolution

:::definition "definition-1.20" (lean := "FABL.ProbabilityDensity, FABL.ProbabilityDensity.toPMF, FABL.ProbabilityDensity.toPMF_apply") (uses := "notation-1.4") (tags := "section-1-5, fidelity-nonnegativity-as-structure-invariant")
*Definition 1.20.* A probability density function on the Hamming cube
$`\mathbb F_2^n` is a nonnegative function
$`\varphi:\mathbb F_2^n\to\mathbb R^{\ge0}` satisfying
$$`\mathbb E_{\boldsymbol{x}\sim\mathbb F_2^n}[\varphi(\boldsymbol{x})]=1.`
The notation $`\boldsymbol{y}\sim\varphi` means that $`\boldsymbol{y}` is drawn
from the associated probability distribution, defined by
$$`\Pr_{\boldsymbol{y}\sim\varphi}[\boldsymbol{y}=y]
=\frac{\varphi(y)}{2^n}
\qquad\text{for every }y\in\mathbb F_2^n.`
:::

:::lemma_ "fact-1.21" (lean := "FABL.ProbabilityDensity.expectation, FABL.ProbabilityDensity.integral_toPMF_eq_expectation, FABL.densityExpectation_eq_uniformInner") (uses := "definition-1.20") (tags := "section-1-5, fidelity-exact")
*Fact 1.21.* If $`\varphi` is a density function and
$`g:\mathbb F_2^n\to\mathbb R`, then
$$`\mathbb E_{\boldsymbol{y}\sim\varphi}[g(\boldsymbol{y})]
=\langle\varphi,g\rangle
=\mathbb E_{\boldsymbol{x}\sim\mathbb F_2^n}
[\varphi(\boldsymbol{x})g(\boldsymbol{x})].`
:::

:::definition "definition-1.22" (lean := "FABL.setIndicator, FABL.subsetDensity") (uses := "definition-1.20") (tags := "section-1-5, fidelity-exact-after-canonical-real-embedding")
*Definition 1.22.* If $`A\subseteq\mathbb F_2^n`, write
$`\mathbf 1_A:\mathbb F_2^n\to\{0,1\}` for its indicator function,
$$`\mathbf 1_A(x)=
\begin{cases}
1 & \text{if }x\in A,\\
0 & \text{if }x\notin A.
\end{cases}`
If $`A\ne\varnothing`, write $`\varphi_A` for the density of the uniform
distribution on $`A`, namely
$$`\varphi_A=\frac{1}{\mathbb E[\mathbf 1_A]}\mathbf 1_A.`
The notation $`\boldsymbol{y}\sim A` abbreviates
$`\boldsymbol{y}\sim\varphi_A`.
:::

:::lemma_ "fact-1.23" (lean := "FABL.binaryFourierCoeff_subsetDensity_singleton_zero, FABL.subsetDensity_singleton_zero_eq_sum_χ") (uses := "definition-1.22") (tags := "section-1-5, fidelity-exact")
*Fact 1.23.* Every Fourier coefficient of $`\varphi_{\{0\}}` is $`1`;
equivalently, its Fourier expansion is
$$`\varphi_{\{0\}}(y)=\sum_{S\subseteq[n]}\chi_S(y).`
:::

:::definition "definition-1.24" (lean := "FABL.convolution, FABL.convolution_apply, FABL.convolution_apply_add, FABL.convolution_apply_swap, FABL.convolution_apply_swap_add") (uses := "notation-1.4") (tags := "section-1-5, fidelity-exact-normalized-convolution")
*Definition 1.24.* Let $`f,g:\mathbb F_2^n\to\mathbb R`. Their convolution
is the function $`f*g:\mathbb F_2^n\to\mathbb R` defined by
$$`(f*g)(x)
=\mathbb E_{\boldsymbol{y}\sim\mathbb F_2^n}
[f(\boldsymbol{y})g(x-\boldsymbol{y})]
=\mathbb E_{\boldsymbol{y}\sim\mathbb F_2^n}
[f(x-\boldsymbol{y})g(\boldsymbol{y})].`
Since subtraction equals addition in $`\mathbb F_2^n`, one may also write
$$`(f*g)(x)
=\mathbb E_{\boldsymbol{y}}[f(\boldsymbol{y})g(x+\boldsymbol{y})]
=\mathbb E_{\boldsymbol{y}}[f(x+\boldsymbol{y})g(\boldsymbol{y})].`
Under the $`\{-1,1\}^n` representation, $`x+y` is replaced by
coordinatewise multiplication $`x\circ y`.
:::

:::lemma_ "support-convolution-laws" (lean := "FABL.convolution_comm, FABL.convolution_assoc") (uses := "definition-1.24") (tags := "section-1-5, support")
*Exercise 1.25.* For functions $`f,g,h:\mathbb F_2^n\to\mathbb R`,
normalized convolution is commutative and associative:
$$`f*g=g*f,
\qquad
f*(g*h)=(f*g)*h.`
:::

:::proposition "proposition-1.25" (lean := "FABL.density_convolution_apply, FABL.densityExpectation_eq_convolution_apply_zero") (uses := "fact-1.21, definition-1.24") (tags := "section-1-5, fidelity-exact")
*Proposition 1.25.* If $`\varphi` is a density function on $`\mathbb F_2^n`
and $`g:\mathbb F_2^n\to\mathbb R`, then for every $`x\in\mathbb F_2^n`,
$$`(\varphi*g)(x)
=\mathbb E_{\boldsymbol{y}\sim\varphi}[g(x-\boldsymbol{y})]
=\mathbb E_{\boldsymbol{y}\sim\varphi}[g(x+\boldsymbol{y})].`
In particular,
$$`\mathbb E_{\boldsymbol{y}\sim\varphi}[g(\boldsymbol{y})]
=(\varphi*g)(0).`
:::

:::proposition "proposition-1.26" (lean := "FABL.ProbabilityDensity.convolution, FABL.ProbabilityDensity.toPMF_convolution, FABL.convolution_probability_eq_add") (uses := "definition-1.20, definition-1.24") (tags := "section-1-5, fidelity-exact-pmf-law-and-event-probability-formula")
*Proposition 1.26.* If $`\varphi` and $`\psi` are probability density
functions on $`\mathbb F_2^n`, then $`\varphi*\psi` is also a probability
density function. It represents the distribution of
$`\boldsymbol{x}=\boldsymbol{y}+\boldsymbol{z}`, where
$`\boldsymbol{y}\sim\varphi` and $`\boldsymbol{z}\sim\psi` are chosen
independently.
:::

:::theorem "theorem-1.27" (lean := "FABL.binaryFourierCoeff_convolution") (uses := "definition-1.24, definition-1.2") (tags := "section-1-5, fidelity-exact")
*Theorem 1.27.* Let $`f,g:\mathbb F_2^n\to\mathbb R`. Then for every
$`S\subseteq[n]`,
$$`\widehat{f*g}(S)=\widehat f(S)\widehat g(S).`
:::
