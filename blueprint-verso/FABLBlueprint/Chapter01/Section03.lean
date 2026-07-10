import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter01.BasicFourierFormulas

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Section 1.3" =>

# 1.3. The orthonormal basis of parity functions

:::definition "definition-1.3" (lean := "FABL.uniformInner, FABL.uniformLpNorm, FABL.uniformLpNorm_two_eq_sqrt_uniformInner") (tags := "section-1-3, fidelity-exact-with-lp-definition-represented-by-Real-rpow")
*Definition 1.3.* For functions $`f,g : \{-1,1\}^n \to \mathbb R`, define
$$`\langle f,g\rangle
=2^{-n}\sum_{x\in\{-1,1\}^n}f(x)g(x)
=\mathbb E_{\boldsymbol{x}\sim\{-1,1\}^n}[f(\boldsymbol{x})g(\boldsymbol{x})].`
Also write
$$`\lVert f\rVert_2=\sqrt{\langle f,f\rangle},
\qquad
\lVert f\rVert_p=\mathbb E[|f(\boldsymbol{x})|^p]^{1/p}.`
:::

:::definition "notation-1.4" (lean := "FABL.uniformPMF, FABL.integral_uniformPMF_eq_expect") (tags := "section-1-3, fidelity-exact")
*Notation 1.4.* The notation $`\boldsymbol{x}\sim\{-1,1\}^n` means that
$`\boldsymbol{x}` is a uniformly chosen random string from $`\{-1,1\}^n`.
Equivalently, the coordinates $`\boldsymbol{x}_i` are independent and each is
$`+1` or $`-1` with probability $`1/2`. Unless another distribution is
specified, $`\Pr` and $`\mathbb E` refer to this uniform choice. Thus the
expectation in Definition 1.3 may be written
$`\mathbb E_{\boldsymbol{x}}[f(\boldsymbol{x})g(\boldsymbol{x})]`,
$`\mathbb E[f(\boldsymbol{x})g(\boldsymbol{x})]`, or $`\mathbb E[fg]`.
:::

:::theorem "theorem-1.5" (lean := "FABL.binaryWalshBasis, FABL.walshBasis, FABL.parity_orthonormal_basis") (uses := "fact-1.6, fact-1.7") (tags := "section-1-3, fidelity-exact-with-explicit-sign-domain")
*Theorem 1.5.* The $`2^n` parity functions
$`\chi_S : \{-1,1\}^n \to \{-1,1\}`, indexed by $`S\subseteq[n]`, form an
orthonormal basis for the real vector space $`V` of functions
$`\{-1,1\}^n\to\mathbb R`; that is,
$$`\langle\chi_S,\chi_T\rangle=
\begin{cases}
1 & \text{if }S=T,\\
0 & \text{if }S\ne T.
\end{cases}`
:::

:::lemma_ "fact-1.6" (lean := "FABL.monomial_mul_monomial") (uses := "support-sign-monomial") (tags := "section-1-3, fidelity-exact")
*Fact 1.6.* For $`x\in\{-1,1\}^n` and $`S,T\subseteq[n]`, one has
$$`\chi_S(x)\chi_T(x)=\chi_{S\mathbin{\triangle}T}(x),`
where $`S\mathbin{\triangle}T` denotes symmetric difference.
:::

:::lemma_ "fact-1.7" (lean := "FABL.expect_monomial") (uses := "notation-1.4") (tags := "section-1-3, fidelity-exact")
*Fact 1.7.* For every $`S\subseteq[n]`, with $`\boldsymbol{x}` uniform on
$`\{-1,1\}^n`,
$$`\mathbb E[\chi_S(\boldsymbol{x})]
=\mathbb E\left[\prod_{i\in S}\boldsymbol{x}_i\right]
=\begin{cases}
1 & \text{if }S=\varnothing,\\
0 & \text{if }S\ne\varnothing.
\end{cases}`
:::
