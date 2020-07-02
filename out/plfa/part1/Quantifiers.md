---
src       : "src/plfa/part1/Quantifiers.lagda.md"
title     : "Quantifiers: Universals and existentials"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
---

{% raw %}<pre class="Agda"><a id="159" class="Keyword">module</a> <a id="166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}" class="Module">plfa.part1.Quantifiers</a> <a id="189" class="Keyword">where</a>
</pre>{% endraw %}
This chapter introduces universal and existential quantification.

## Imports

{% raw %}<pre class="Agda"><a id="283" class="Keyword">import</a> <a id="290" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="328" class="Symbol">as</a> <a id="331" class="Module">Eq</a>
<a id="334" class="Keyword">open</a> <a id="339" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="342" class="Keyword">using</a> <a id="348" class="Symbol">(</a><a id="349" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="352" class="Symbol">;</a> <a id="354" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="358" class="Symbol">)</a>
<a id="360" class="Keyword">open</a> <a id="365" class="Keyword">import</a> <a id="372" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="381" class="Keyword">using</a> <a id="387" class="Symbol">(</a><a id="388" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="389" class="Symbol">;</a> <a id="391" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="395" class="Symbol">;</a> <a id="397" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="400" class="Symbol">;</a> <a id="402" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="405" class="Symbol">;</a> <a id="407" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="410" class="Symbol">)</a>
<a id="412" class="Keyword">open</a> <a id="417" class="Keyword">import</a> <a id="424" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="441" class="Keyword">using</a> <a id="447" class="Symbol">(</a><a id="448" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="450" class="Symbol">)</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="477" class="Keyword">using</a> <a id="483" class="Symbol">(</a><a id="484" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="487" class="Symbol">;</a> <a id="489" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="494" class="Symbol">;</a> <a id="496" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="501" class="Symbol">)</a> <a id="503" class="Keyword">renaming</a> <a id="512" class="Symbol">(</a><a id="513" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="517" class="Symbol">to</a> <a id="520" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="525" class="Symbol">)</a>
<a id="527" class="Keyword">open</a> <a id="532" class="Keyword">import</a> <a id="539" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="548" class="Keyword">using</a> <a id="554" class="Symbol">(</a><a id="555" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="558" class="Symbol">;</a> <a id="560" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="564" class="Symbol">;</a> <a id="566" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="570" class="Symbol">)</a>
<a id="572" class="Keyword">open</a> <a id="577" class="Keyword">import</a> <a id="584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="607" class="Keyword">using</a> <a id="613" class="Symbol">(</a><a id="614" href="plfa.part1.Isomorphism.html#4365" class="Record Operator">_≃_</a><a id="617" class="Symbol">;</a> <a id="619" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a><a id="633" class="Symbol">)</a>
</pre>{% endraw %}

## Universals

We formalise universal quantification using the dependent function
type, which has appeared throughout this book.  For instance, in
Chapter Induction we showed addition is associative:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

which asserts for all natural numbers `m`, `n`, and `p`
that `(m + n) + p ≡ m + (n + p)` holds.  It is a dependent
function, which given values for `m`, `n`, and `p` returns
evidence for the corresponding equation.

In general, given a variable `x` of type `A` and a proposition `B x`
which contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type `A`
the proposition `B M` holds.  Here `B M` stands for the proposition
`B x` with each free occurrence of `x` replaced by `M`.  Variable `x`
appears free in `B x` but bound in `∀ (x : A) → B x`.

Evidence that `∀ (x : A) → B x` holds is of the form

    λ (x : A) → N x

where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L
M` provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.

Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
{% raw %}<pre class="Agda"><a id="∀-elim"></a><a id="2111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2111" class="Function">∀-elim</a> <a id="2118" class="Symbol">:</a> <a id="2120" class="Symbol">∀</a> <a id="2122" class="Symbol">{</a><a id="2123" href="plfa.part1.Quantifiers.html#2123" class="Bound">A</a> <a id="2125" class="Symbol">:</a> <a id="2127" class="PrimitiveType">Set</a><a id="2130" class="Symbol">}</a> <a id="2132" class="Symbol">{</a><a id="2133" href="plfa.part1.Quantifiers.html#2133" class="Bound">B</a> <a id="2135" class="Symbol">:</a> <a id="2137" href="plfa.part1.Quantifiers.html#2123" class="Bound">A</a> <a id="2139" class="Symbol">→</a> <a id="2141" class="PrimitiveType">Set</a><a id="2144" class="Symbol">}</a>
  <a id="2148" class="Symbol">→</a> <a id="2150" class="Symbol">(</a><a id="2151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2151" class="Bound">L</a> <a id="2153" class="Symbol">:</a> <a id="2155" class="Symbol">∀</a> <a id="2157" class="Symbol">(</a><a id="2158" href="plfa.part1.Quantifiers.html#2158" class="Bound">x</a> <a id="2160" class="Symbol">:</a> <a id="2162" href="plfa.part1.Quantifiers.html#2123" class="Bound">A</a><a id="2163" class="Symbol">)</a> <a id="2165" class="Symbol">→</a> <a id="2167" href="plfa.part1.Quantifiers.html#2133" class="Bound">B</a> <a id="2169" href="plfa.part1.Quantifiers.html#2158" class="Bound">x</a><a id="2170" class="Symbol">)</a>
  <a id="2174" class="Symbol">→</a> <a id="2176" class="Symbol">(</a><a id="2177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2177" class="Bound">M</a> <a id="2179" class="Symbol">:</a> <a id="2181" href="plfa.part1.Quantifiers.html#2123" class="Bound">A</a><a id="2182" class="Symbol">)</a>
    <a id="2188" class="Comment">-----------------</a>
  <a id="2208" class="Symbol">→</a> <a id="2210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2133" class="Bound">B</a> <a id="2212" href="plfa.part1.Quantifiers.html#2177" class="Bound">M</a>
<a id="2214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2111" class="Function">∀-elim</a> <a id="2221" href="plfa.part1.Quantifiers.html#2221" class="Bound">L</a> <a id="2223" href="plfa.part1.Quantifiers.html#2223" class="Bound">M</a> <a id="2225" class="Symbol">=</a> <a id="2227" href="plfa.part1.Quantifiers.html#2221" class="Bound">L</a> <a id="2229" href="plfa.part1.Quantifiers.html#2223" class="Bound">M</a>
</pre>{% endraw %}As with `→-elim`, the rule corresponds to function application.

Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.

Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
{% raw %}<pre class="Agda"><a id="3493" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="3505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3505" class="Postulate">∀-distrib-×</a> <a id="3517" class="Symbol">:</a> <a id="3519" class="Symbol">∀</a> <a id="3521" class="Symbol">{</a><a id="3522" href="plfa.part1.Quantifiers.html#3522" class="Bound">A</a> <a id="3524" class="Symbol">:</a> <a id="3526" class="PrimitiveType">Set</a><a id="3529" class="Symbol">}</a> <a id="3531" class="Symbol">{</a><a id="3532" href="plfa.part1.Quantifiers.html#3532" class="Bound">B</a> <a id="3534" href="plfa.part1.Quantifiers.html#3534" class="Bound">C</a> <a id="3536" class="Symbol">:</a> <a id="3538" href="plfa.part1.Quantifiers.html#3522" class="Bound">A</a> <a id="3540" class="Symbol">→</a> <a id="3542" class="PrimitiveType">Set</a><a id="3545" class="Symbol">}</a> <a id="3547" class="Symbol">→</a>
    <a id="3553" class="Symbol">(∀</a> <a id="3556" class="Symbol">(</a><a id="3557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3557" class="Bound">x</a> <a id="3559" class="Symbol">:</a> <a id="3561" href="plfa.part1.Quantifiers.html#3522" class="Bound">A</a><a id="3562" class="Symbol">)</a> <a id="3564" class="Symbol">→</a> <a id="3566" href="plfa.part1.Quantifiers.html#3532" class="Bound">B</a> <a id="3568" href="plfa.part1.Quantifiers.html#3557" class="Bound">x</a> <a id="3570" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3572" href="plfa.part1.Quantifiers.html#3534" class="Bound">C</a> <a id="3574" href="plfa.part1.Quantifiers.html#3557" class="Bound">x</a><a id="3575" class="Symbol">)</a> <a id="3577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="3579" class="Symbol">(∀</a> <a id="3582" class="Symbol">(</a><a id="3583" href="plfa.part1.Quantifiers.html#3583" class="Bound">x</a> <a id="3585" class="Symbol">:</a> <a id="3587" href="plfa.part1.Quantifiers.html#3522" class="Bound">A</a><a id="3588" class="Symbol">)</a> <a id="3590" class="Symbol">→</a> <a id="3592" href="plfa.part1.Quantifiers.html#3532" class="Bound">B</a> <a id="3594" href="plfa.part1.Quantifiers.html#3583" class="Bound">x</a><a id="3595" class="Symbol">)</a> <a id="3597" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3599" class="Symbol">(∀</a> <a id="3602" class="Symbol">(</a><a id="3603" href="plfa.part1.Quantifiers.html#3603" class="Bound">x</a> <a id="3605" class="Symbol">:</a> <a id="3607" href="plfa.part1.Quantifiers.html#3522" class="Bound">A</a><a id="3608" class="Symbol">)</a> <a id="3610" class="Symbol">→</a> <a id="3612" href="plfa.part1.Quantifiers.html#3534" class="Bound">C</a> <a id="3614" href="plfa.part1.Quantifiers.html#3603" class="Bound">x</a><a id="3615" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}/Connectives/).

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
{% raw %}<pre class="Agda"><a id="3847" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="3859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3859" class="Postulate">⊎∀-implies-∀⊎</a> <a id="3873" class="Symbol">:</a> <a id="3875" class="Symbol">∀</a> <a id="3877" class="Symbol">{</a><a id="3878" href="plfa.part1.Quantifiers.html#3878" class="Bound">A</a> <a id="3880" class="Symbol">:</a> <a id="3882" class="PrimitiveType">Set</a><a id="3885" class="Symbol">}</a> <a id="3887" class="Symbol">{</a><a id="3888" href="plfa.part1.Quantifiers.html#3888" class="Bound">B</a> <a id="3890" href="plfa.part1.Quantifiers.html#3890" class="Bound">C</a> <a id="3892" class="Symbol">:</a> <a id="3894" href="plfa.part1.Quantifiers.html#3878" class="Bound">A</a> <a id="3896" class="Symbol">→</a> <a id="3898" class="PrimitiveType">Set</a><a id="3901" class="Symbol">}</a> <a id="3903" class="Symbol">→</a>
    <a id="3909" class="Symbol">(∀</a> <a id="3912" class="Symbol">(</a><a id="3913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3913" class="Bound">x</a> <a id="3915" class="Symbol">:</a> <a id="3917" href="plfa.part1.Quantifiers.html#3878" class="Bound">A</a><a id="3918" class="Symbol">)</a> <a id="3920" class="Symbol">→</a> <a id="3922" href="plfa.part1.Quantifiers.html#3888" class="Bound">B</a> <a id="3924" href="plfa.part1.Quantifiers.html#3913" class="Bound">x</a><a id="3925" class="Symbol">)</a> <a id="3927" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3929" class="Symbol">(∀</a> <a id="3932" class="Symbol">(</a><a id="3933" href="plfa.part1.Quantifiers.html#3933" class="Bound">x</a> <a id="3935" class="Symbol">:</a> <a id="3937" href="plfa.part1.Quantifiers.html#3878" class="Bound">A</a><a id="3938" class="Symbol">)</a> <a id="3940" class="Symbol">→</a> <a id="3942" href="plfa.part1.Quantifiers.html#3890" class="Bound">C</a> <a id="3944" href="plfa.part1.Quantifiers.html#3933" class="Bound">x</a><a id="3945" class="Symbol">)</a>  <a id="3948" class="Symbol">→</a>  <a id="3951" class="Symbol">∀</a> <a id="3953" class="Symbol">(</a><a id="3954" href="plfa.part1.Quantifiers.html#3954" class="Bound">x</a> <a id="3956" class="Symbol">:</a> <a id="3958" href="plfa.part1.Quantifiers.html#3878" class="Bound">A</a><a id="3959" class="Symbol">)</a> <a id="3961" class="Symbol">→</a> <a id="3963" href="plfa.part1.Quantifiers.html#3888" class="Bound">B</a> <a id="3965" href="plfa.part1.Quantifiers.html#3954" class="Bound">x</a> <a id="3967" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3969" href="plfa.part1.Quantifiers.html#3890" class="Bound">C</a> <a id="3971" href="plfa.part1.Quantifiers.html#3954" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
{% raw %}<pre class="Agda"><a id="4103" class="Keyword">data</a> <a id="Tri"></a><a id="4108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4108" class="Datatype">Tri</a> <a id="4112" class="Symbol">:</a> <a id="4114" class="PrimitiveType">Set</a> <a id="4118" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="4126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4126" class="InductiveConstructor">aa</a> <a id="4129" class="Symbol">:</a> <a id="4131" href="plfa.part1.Quantifiers.html#4108" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="4137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4137" class="InductiveConstructor">bb</a> <a id="4140" class="Symbol">:</a> <a id="4142" href="plfa.part1.Quantifiers.html#4108" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="4148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4148" class="InductiveConstructor">cc</a> <a id="4151" class="Symbol">:</a> <a id="4153" href="plfa.part1.Quantifiers.html#4108" class="Datatype">Tri</a>
</pre>{% endraw %}Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
Hint: you will need to postulate a version of extensionality that
works for dependent functions.


## Existentials

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.

We formalise existential quantification by declaring a suitable
inductive type:
{% raw %}<pre class="Agda"><a id="4876" class="Keyword">data</a> <a id="Σ"></a><a id="4881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4881" class="Datatype">Σ</a> <a id="4883" class="Symbol">(</a><a id="4884" href="plfa.part1.Quantifiers.html#4884" class="Bound">A</a> <a id="4886" class="Symbol">:</a> <a id="4888" class="PrimitiveType">Set</a><a id="4891" class="Symbol">)</a> <a id="4893" class="Symbol">(</a><a id="4894" href="plfa.part1.Quantifiers.html#4894" class="Bound">B</a> <a id="4896" class="Symbol">:</a> <a id="4898" href="plfa.part1.Quantifiers.html#4884" class="Bound">A</a> <a id="4900" class="Symbol">→</a> <a id="4902" class="PrimitiveType">Set</a><a id="4905" class="Symbol">)</a> <a id="4907" class="Symbol">:</a> <a id="4909" class="PrimitiveType">Set</a> <a id="4913" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="4921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4921" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="4927" class="Symbol">:</a> <a id="4929" class="Symbol">(</a><a id="4930" href="plfa.part1.Quantifiers.html#4930" class="Bound">x</a> <a id="4932" class="Symbol">:</a> <a id="4934" href="plfa.part1.Quantifiers.html#4884" class="Bound">A</a><a id="4935" class="Symbol">)</a> <a id="4937" class="Symbol">→</a> <a id="4939" href="plfa.part1.Quantifiers.html#4894" class="Bound">B</a> <a id="4941" href="plfa.part1.Quantifiers.html#4930" class="Bound">x</a> <a id="4943" class="Symbol">→</a> <a id="4945" href="plfa.part1.Quantifiers.html#4881" class="Datatype">Σ</a> <a id="4947" href="plfa.part1.Quantifiers.html#4884" class="Bound">A</a> <a id="4949" href="plfa.part1.Quantifiers.html#4894" class="Bound">B</a>
</pre>{% endraw %}We define a convenient syntax for existentials as follows:
{% raw %}<pre class="Agda"><a id="Σ-syntax"></a><a id="5018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5018" class="Function">Σ-syntax</a> <a id="5027" class="Symbol">=</a> <a id="5029" href="plfa.part1.Quantifiers.html#4881" class="Datatype">Σ</a>
<a id="5031" class="Keyword">infix</a> <a id="5037" class="Number">2</a> <a id="5039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5018" class="Function">Σ-syntax</a>
<a id="5048" class="Keyword">syntax</a> <a id="5055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5018" class="Function">Σ-syntax</a> <a id="5064" class="Bound">A</a> <a id="5066" class="Symbol">(λ</a> <a id="5069" class="Bound">x</a> <a id="5071" class="Symbol">→</a> <a id="5073" class="Bound">B</a><a id="5074" class="Symbol">)</a> <a id="5076" class="Symbol">=</a> <a id="5078" class="Function">Σ[</a> <a id="5081" class="Bound">x</a> <a id="5083" class="Function">∈</a> <a id="5085" class="Bound">A</a> <a id="5087" class="Function">]</a> <a id="5089" class="Bound">B</a>
</pre>{% endraw %}This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type:
{% raw %}<pre class="Agda"><a id="5518" class="Keyword">record</a> <a id="Σ′"></a><a id="5525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5525" class="Record">Σ′</a> <a id="5528" class="Symbol">(</a><a id="5529" href="plfa.part1.Quantifiers.html#5529" class="Bound">A</a> <a id="5531" class="Symbol">:</a> <a id="5533" class="PrimitiveType">Set</a><a id="5536" class="Symbol">)</a> <a id="5538" class="Symbol">(</a><a id="5539" href="plfa.part1.Quantifiers.html#5539" class="Bound">B</a> <a id="5541" class="Symbol">:</a> <a id="5543" href="plfa.part1.Quantifiers.html#5529" class="Bound">A</a> <a id="5545" class="Symbol">→</a> <a id="5547" class="PrimitiveType">Set</a><a id="5550" class="Symbol">)</a> <a id="5552" class="Symbol">:</a> <a id="5554" class="PrimitiveType">Set</a> <a id="5558" class="Keyword">where</a>
  <a id="5566" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="5576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5576" class="Field">proj₁′</a> <a id="5583" class="Symbol">:</a> <a id="5585" href="plfa.part1.Quantifiers.html#5529" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="5591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5591" class="Field">proj₂′</a> <a id="5598" class="Symbol">:</a> <a id="5600" href="plfa.part1.Quantifiers.html#5539" class="Bound">B</a> <a id="5602" href="plfa.part1.Quantifiers.html#5576" class="Field">proj₁′</a>
</pre>{% endraw %}Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B M`.

Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.

Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.

Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.

A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
{% raw %}<pre class="Agda"><a id="∃"></a><a id="7249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7249" class="Function">∃</a> <a id="7251" class="Symbol">:</a> <a id="7253" class="Symbol">∀</a> <a id="7255" class="Symbol">{</a><a id="7256" href="plfa.part1.Quantifiers.html#7256" class="Bound">A</a> <a id="7258" class="Symbol">:</a> <a id="7260" class="PrimitiveType">Set</a><a id="7263" class="Symbol">}</a> <a id="7265" class="Symbol">(</a><a id="7266" href="plfa.part1.Quantifiers.html#7266" class="Bound">B</a> <a id="7268" class="Symbol">:</a> <a id="7270" href="plfa.part1.Quantifiers.html#7256" class="Bound">A</a> <a id="7272" class="Symbol">→</a> <a id="7274" class="PrimitiveType">Set</a><a id="7277" class="Symbol">)</a> <a id="7279" class="Symbol">→</a> <a id="7281" class="PrimitiveType">Set</a>
<a id="7285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7249" class="Function">∃</a> <a id="7287" class="Symbol">{</a><a id="7288" href="plfa.part1.Quantifiers.html#7288" class="Bound">A</a><a id="7289" class="Symbol">}</a> <a id="7291" href="plfa.part1.Quantifiers.html#7291" class="Bound">B</a> <a id="7293" class="Symbol">=</a> <a id="7295" href="plfa.part1.Quantifiers.html#4881" class="Datatype">Σ</a> <a id="7297" href="plfa.part1.Quantifiers.html#7288" class="Bound">A</a> <a id="7299" href="plfa.part1.Quantifiers.html#7291" class="Bound">B</a>

<a id="∃-syntax"></a><a id="7302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7302" class="Function">∃-syntax</a> <a id="7311" class="Symbol">=</a> <a id="7313" href="plfa.part1.Quantifiers.html#7249" class="Function">∃</a>
<a id="7315" class="Keyword">syntax</a> <a id="7322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7302" class="Function">∃-syntax</a> <a id="7331" class="Symbol">(λ</a> <a id="7334" class="Bound">x</a> <a id="7336" class="Symbol">→</a> <a id="7338" class="Bound">B</a><a id="7339" class="Symbol">)</a> <a id="7341" class="Symbol">=</a> <a id="7343" class="Function">∃[</a> <a id="7346" class="Bound">x</a> <a id="7348" class="Function">]</a> <a id="7350" class="Bound">B</a>
</pre>{% endraw %}The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{% raw %}<pre class="Agda"><a id="∃-elim"></a><a id="7684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7684" class="Function">∃-elim</a> <a id="7691" class="Symbol">:</a> <a id="7693" class="Symbol">∀</a> <a id="7695" class="Symbol">{</a><a id="7696" href="plfa.part1.Quantifiers.html#7696" class="Bound">A</a> <a id="7698" class="Symbol">:</a> <a id="7700" class="PrimitiveType">Set</a><a id="7703" class="Symbol">}</a> <a id="7705" class="Symbol">{</a><a id="7706" href="plfa.part1.Quantifiers.html#7706" class="Bound">B</a> <a id="7708" class="Symbol">:</a> <a id="7710" href="plfa.part1.Quantifiers.html#7696" class="Bound">A</a> <a id="7712" class="Symbol">→</a> <a id="7714" class="PrimitiveType">Set</a><a id="7717" class="Symbol">}</a> <a id="7719" class="Symbol">{</a><a id="7720" href="plfa.part1.Quantifiers.html#7720" class="Bound">C</a> <a id="7722" class="Symbol">:</a> <a id="7724" class="PrimitiveType">Set</a><a id="7727" class="Symbol">}</a>
  <a id="7731" class="Symbol">→</a> <a id="7733" class="Symbol">(∀</a> <a id="7736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7736" class="Bound">x</a> <a id="7738" class="Symbol">→</a> <a id="7740" href="plfa.part1.Quantifiers.html#7706" class="Bound">B</a> <a id="7742" href="plfa.part1.Quantifiers.html#7736" class="Bound">x</a> <a id="7744" class="Symbol">→</a> <a id="7746" href="plfa.part1.Quantifiers.html#7720" class="Bound">C</a><a id="7747" class="Symbol">)</a>
  <a id="7751" class="Symbol">→</a> <a id="7753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7302" class="Function">∃[</a> <a id="7756" href="plfa.part1.Quantifiers.html#7756" class="Bound">x</a> <a id="7758" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="7760" href="plfa.part1.Quantifiers.html#7706" class="Bound">B</a> <a id="7762" href="plfa.part1.Quantifiers.html#7756" class="Bound">x</a>
    <a id="7768" class="Comment">---------------</a>
  <a id="7786" class="Symbol">→</a> <a id="7788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7720" class="Bound">C</a>
<a id="7790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7684" class="Function">∃-elim</a> <a id="7797" href="plfa.part1.Quantifiers.html#7797" class="Bound">f</a> <a id="7799" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="7801" href="plfa.part1.Quantifiers.html#7801" class="Bound">x</a> <a id="7803" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="7805" href="plfa.part1.Quantifiers.html#7805" class="Bound">y</a> <a id="7807" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a> <a id="7809" class="Symbol">=</a> <a id="7811" href="plfa.part1.Quantifiers.html#7797" class="Bound">f</a> <a id="7813" href="plfa.part1.Quantifiers.html#7801" class="Bound">x</a> <a id="7815" href="plfa.part1.Quantifiers.html#7805" class="Bound">y</a>
</pre>{% endraw %}In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
{% raw %}<pre class="Agda"><a id="∀∃-currying"></a><a id="8265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8265" class="Function">∀∃-currying</a> <a id="8277" class="Symbol">:</a> <a id="8279" class="Symbol">∀</a> <a id="8281" class="Symbol">{</a><a id="8282" href="plfa.part1.Quantifiers.html#8282" class="Bound">A</a> <a id="8284" class="Symbol">:</a> <a id="8286" class="PrimitiveType">Set</a><a id="8289" class="Symbol">}</a> <a id="8291" class="Symbol">{</a><a id="8292" href="plfa.part1.Quantifiers.html#8292" class="Bound">B</a> <a id="8294" class="Symbol">:</a> <a id="8296" href="plfa.part1.Quantifiers.html#8282" class="Bound">A</a> <a id="8298" class="Symbol">→</a> <a id="8300" class="PrimitiveType">Set</a><a id="8303" class="Symbol">}</a> <a id="8305" class="Symbol">{</a><a id="8306" href="plfa.part1.Quantifiers.html#8306" class="Bound">C</a> <a id="8308" class="Symbol">:</a> <a id="8310" class="PrimitiveType">Set</a><a id="8313" class="Symbol">}</a>
  <a id="8317" class="Symbol">→</a> <a id="8319" class="Symbol">(∀</a> <a id="8322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8322" class="Bound">x</a> <a id="8324" class="Symbol">→</a> <a id="8326" href="plfa.part1.Quantifiers.html#8292" class="Bound">B</a> <a id="8328" href="plfa.part1.Quantifiers.html#8322" class="Bound">x</a> <a id="8330" class="Symbol">→</a> <a id="8332" href="plfa.part1.Quantifiers.html#8306" class="Bound">C</a><a id="8333" class="Symbol">)</a> <a id="8335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8337" class="Symbol">(</a><a id="8338" href="plfa.part1.Quantifiers.html#7302" class="Function">∃[</a> <a id="8341" href="plfa.part1.Quantifiers.html#8341" class="Bound">x</a> <a id="8343" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="8345" href="plfa.part1.Quantifiers.html#8292" class="Bound">B</a> <a id="8347" href="plfa.part1.Quantifiers.html#8341" class="Bound">x</a> <a id="8349" class="Symbol">→</a> <a id="8351" href="plfa.part1.Quantifiers.html#8306" class="Bound">C</a><a id="8352" class="Symbol">)</a>
<a id="8354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8265" class="Function">∀∃-currying</a> <a id="8366" class="Symbol">=</a>
  <a id="8370" class="Keyword">record</a>
    <a id="8381" class="Symbol">{</a> <a id="8383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="8391" class="Symbol">=</a>  <a id="8394" class="Symbol">λ{</a> <a id="8397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8397" class="Bound">f</a> <a id="8399" class="Symbol">→</a> <a id="8401" class="Symbol">λ{</a> <a id="8404" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="8406" href="plfa.part1.Quantifiers.html#8406" class="Bound">x</a> <a id="8408" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="8410" href="plfa.part1.Quantifiers.html#8410" class="Bound">y</a> <a id="8412" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a> <a id="8414" class="Symbol">→</a> <a id="8416" href="plfa.part1.Quantifiers.html#8397" class="Bound">f</a> <a id="8418" href="plfa.part1.Quantifiers.html#8406" class="Bound">x</a> <a id="8420" href="plfa.part1.Quantifiers.html#8410" class="Bound">y</a> <a id="8422" class="Symbol">}}</a>
    <a id="8429" class="Symbol">;</a> <a id="8431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="8439" class="Symbol">=</a>  <a id="8442" class="Symbol">λ{</a> <a id="8445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8445" class="Bound">g</a> <a id="8447" class="Symbol">→</a> <a id="8449" class="Symbol">λ{</a> <a id="8452" href="plfa.part1.Quantifiers.html#8452" class="Bound">x</a> <a id="8454" class="Symbol">→</a> <a id="8456" class="Symbol">λ{</a> <a id="8459" href="plfa.part1.Quantifiers.html#8459" class="Bound">y</a> <a id="8461" class="Symbol">→</a> <a id="8463" href="plfa.part1.Quantifiers.html#8445" class="Bound">g</a> <a id="8465" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="8467" href="plfa.part1.Quantifiers.html#8452" class="Bound">x</a> <a id="8469" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="8471" href="plfa.part1.Quantifiers.html#8459" class="Bound">y</a> <a id="8473" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a> <a id="8475" class="Symbol">}}}</a>
    <a id="8483" class="Symbol">;</a> <a id="8485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="8493" class="Symbol">=</a>  <a id="8496" class="Symbol">λ{</a> <a id="8499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8499" class="Bound">f</a> <a id="8501" class="Symbol">→</a> <a id="8503" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8508" class="Symbol">}</a>
    <a id="8514" class="Symbol">;</a> <a id="8516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="8524" class="Symbol">=</a>  <a id="8527" class="Symbol">λ{</a> <a id="8530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8530" class="Bound">g</a> <a id="8532" class="Symbol">→</a> <a id="8534" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="8549" class="Symbol">λ{</a> <a id="8552" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="8554" href="plfa.part1.Quantifiers.html#8554" class="Bound">x</a> <a id="8556" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="8558" href="plfa.part1.Quantifiers.html#8558" class="Bound">y</a> <a id="8560" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a> <a id="8562" class="Symbol">→</a> <a id="8564" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8569" class="Symbol">}}</a>
    <a id="8576" class="Symbol">}</a>
</pre>{% endraw %}The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication]({{ site.baseurl }}/Connectives/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
{% raw %}<pre class="Agda"><a id="8893" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="8905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8905" class="Postulate">∃-distrib-⊎</a> <a id="8917" class="Symbol">:</a> <a id="8919" class="Symbol">∀</a> <a id="8921" class="Symbol">{</a><a id="8922" href="plfa.part1.Quantifiers.html#8922" class="Bound">A</a> <a id="8924" class="Symbol">:</a> <a id="8926" class="PrimitiveType">Set</a><a id="8929" class="Symbol">}</a> <a id="8931" class="Symbol">{</a><a id="8932" href="plfa.part1.Quantifiers.html#8932" class="Bound">B</a> <a id="8934" href="plfa.part1.Quantifiers.html#8934" class="Bound">C</a> <a id="8936" class="Symbol">:</a> <a id="8938" href="plfa.part1.Quantifiers.html#8922" class="Bound">A</a> <a id="8940" class="Symbol">→</a> <a id="8942" class="PrimitiveType">Set</a><a id="8945" class="Symbol">}</a> <a id="8947" class="Symbol">→</a>
    <a id="8953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7302" class="Function">∃[</a> <a id="8956" href="plfa.part1.Quantifiers.html#8956" class="Bound">x</a> <a id="8958" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="8960" class="Symbol">(</a><a id="8961" href="plfa.part1.Quantifiers.html#8932" class="Bound">B</a> <a id="8963" href="plfa.part1.Quantifiers.html#8956" class="Bound">x</a> <a id="8965" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8967" href="plfa.part1.Quantifiers.html#8934" class="Bound">C</a> <a id="8969" href="plfa.part1.Quantifiers.html#8956" class="Bound">x</a><a id="8970" class="Symbol">)</a> <a id="8972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8974" class="Symbol">(</a><a id="8975" href="plfa.part1.Quantifiers.html#7302" class="Function">∃[</a> <a id="8978" href="plfa.part1.Quantifiers.html#8978" class="Bound">x</a> <a id="8980" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="8982" href="plfa.part1.Quantifiers.html#8932" class="Bound">B</a> <a id="8984" href="plfa.part1.Quantifiers.html#8978" class="Bound">x</a><a id="8985" class="Symbol">)</a> <a id="8987" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8989" class="Symbol">(</a><a id="8990" href="plfa.part1.Quantifiers.html#7302" class="Function">∃[</a> <a id="8993" href="plfa.part1.Quantifiers.html#8993" class="Bound">x</a> <a id="8995" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="8997" href="plfa.part1.Quantifiers.html#8934" class="Bound">C</a> <a id="8999" href="plfa.part1.Quantifiers.html#8993" class="Bound">x</a><a id="9000" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
{% raw %}<pre class="Agda"><a id="9133" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="9145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9145" class="Postulate">∃×-implies-×∃</a> <a id="9159" class="Symbol">:</a> <a id="9161" class="Symbol">∀</a> <a id="9163" class="Symbol">{</a><a id="9164" href="plfa.part1.Quantifiers.html#9164" class="Bound">A</a> <a id="9166" class="Symbol">:</a> <a id="9168" class="PrimitiveType">Set</a><a id="9171" class="Symbol">}</a> <a id="9173" class="Symbol">{</a><a id="9174" href="plfa.part1.Quantifiers.html#9174" class="Bound">B</a> <a id="9176" href="plfa.part1.Quantifiers.html#9176" class="Bound">C</a> <a id="9178" class="Symbol">:</a> <a id="9180" href="plfa.part1.Quantifiers.html#9164" class="Bound">A</a> <a id="9182" class="Symbol">→</a> <a id="9184" class="PrimitiveType">Set</a><a id="9187" class="Symbol">}</a> <a id="9189" class="Symbol">→</a>
    <a id="9195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7302" class="Function">∃[</a> <a id="9198" href="plfa.part1.Quantifiers.html#9198" class="Bound">x</a> <a id="9200" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="9202" class="Symbol">(</a><a id="9203" href="plfa.part1.Quantifiers.html#9174" class="Bound">B</a> <a id="9205" href="plfa.part1.Quantifiers.html#9198" class="Bound">x</a> <a id="9207" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="9209" href="plfa.part1.Quantifiers.html#9176" class="Bound">C</a> <a id="9211" href="plfa.part1.Quantifiers.html#9198" class="Bound">x</a><a id="9212" class="Symbol">)</a> <a id="9214" class="Symbol">→</a> <a id="9216" class="Symbol">(</a><a id="9217" href="plfa.part1.Quantifiers.html#7302" class="Function">∃[</a> <a id="9220" href="plfa.part1.Quantifiers.html#9220" class="Bound">x</a> <a id="9222" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="9224" href="plfa.part1.Quantifiers.html#9174" class="Bound">B</a> <a id="9226" href="plfa.part1.Quantifiers.html#9220" class="Bound">x</a><a id="9227" class="Symbol">)</a> <a id="9229" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="9231" class="Symbol">(</a><a id="9232" href="plfa.part1.Quantifiers.html#7302" class="Function">∃[</a> <a id="9235" href="plfa.part1.Quantifiers.html#9235" class="Bound">x</a> <a id="9237" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="9239" href="plfa.part1.Quantifiers.html#9176" class="Bound">C</a> <a id="9241" href="plfa.part1.Quantifiers.html#9235" class="Bound">x</a><a id="9242" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations]({{ site.baseurl }}/Relations/):
{% raw %}<pre class="Agda"><a id="9578" class="Keyword">data</a> <a id="even"></a><a id="9583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9583" class="Datatype">even</a> <a id="9588" class="Symbol">:</a> <a id="9590" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9592" class="Symbol">→</a> <a id="9594" class="PrimitiveType">Set</a>
<a id="9598" class="Keyword">data</a> <a id="odd"></a><a id="9603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9603" class="Datatype">odd</a>  <a id="9608" class="Symbol">:</a> <a id="9610" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9612" class="Symbol">→</a> <a id="9614" class="PrimitiveType">Set</a>

<a id="9619" class="Keyword">data</a> <a id="9624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9583" class="Datatype">even</a> <a id="9629" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="9638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9638" class="InductiveConstructor">even-zero</a> <a id="9648" class="Symbol">:</a> <a id="9650" href="plfa.part1.Quantifiers.html#9583" class="Datatype">even</a> <a id="9655" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="9663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9663" class="InductiveConstructor">even-suc</a> <a id="9672" class="Symbol">:</a> <a id="9674" class="Symbol">∀</a> <a id="9676" class="Symbol">{</a><a id="9677" href="plfa.part1.Quantifiers.html#9677" class="Bound">n</a> <a id="9679" class="Symbol">:</a> <a id="9681" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9682" class="Symbol">}</a>
    <a id="9688" class="Symbol">→</a> <a id="9690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9603" class="Datatype">odd</a> <a id="9694" href="plfa.part1.Quantifiers.html#9677" class="Bound">n</a>
      <a id="9702" class="Comment">------------</a>
    <a id="9719" class="Symbol">→</a> <a id="9721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9583" class="Datatype">even</a> <a id="9726" class="Symbol">(</a><a id="9727" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9731" href="plfa.part1.Quantifiers.html#9677" class="Bound">n</a><a id="9732" class="Symbol">)</a>

<a id="9735" class="Keyword">data</a> <a id="9740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9603" class="Datatype">odd</a> <a id="9744" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="9752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9752" class="InductiveConstructor">odd-suc</a> <a id="9760" class="Symbol">:</a> <a id="9762" class="Symbol">∀</a> <a id="9764" class="Symbol">{</a><a id="9765" href="plfa.part1.Quantifiers.html#9765" class="Bound">n</a> <a id="9767" class="Symbol">:</a> <a id="9769" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9770" class="Symbol">}</a>
    <a id="9776" class="Symbol">→</a> <a id="9778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9583" class="Datatype">even</a> <a id="9783" href="plfa.part1.Quantifiers.html#9765" class="Bound">n</a>
      <a id="9791" class="Comment">-----------</a>
    <a id="9807" class="Symbol">→</a> <a id="9809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9603" class="Datatype">odd</a> <a id="9813" class="Symbol">(</a><a id="9814" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9818" href="plfa.part1.Quantifiers.html#9765" class="Bound">n</a><a id="9819" class="Symbol">)</a>
</pre>{% endraw %}A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.

We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:

`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`

By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.

Here is the proof in the forward direction:
{% raw %}<pre class="Agda"><a id="even-∃"></a><a id="10440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10440" class="Function">even-∃</a> <a id="10447" class="Symbol">:</a> <a id="10449" class="Symbol">∀</a> <a id="10451" class="Symbol">{</a><a id="10452" href="plfa.part1.Quantifiers.html#10452" class="Bound">n</a> <a id="10454" class="Symbol">:</a> <a id="10456" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10457" class="Symbol">}</a> <a id="10459" class="Symbol">→</a> <a id="10461" href="plfa.part1.Quantifiers.html#9583" class="Datatype">even</a> <a id="10466" href="plfa.part1.Quantifiers.html#10452" class="Bound">n</a> <a id="10468" class="Symbol">→</a> <a id="10470" href="plfa.part1.Quantifiers.html#7302" class="Function">∃[</a> <a id="10473" href="plfa.part1.Quantifiers.html#10473" class="Bound">m</a> <a id="10475" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="10477" class="Symbol">(</a>    <a id="10482" href="plfa.part1.Quantifiers.html#10473" class="Bound">m</a> <a id="10484" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="10486" class="Number">2</a> <a id="10488" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10490" href="plfa.part1.Quantifiers.html#10452" class="Bound">n</a><a id="10491" class="Symbol">)</a>
<a id="odd-∃"></a><a id="10493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10493" class="Function">odd-∃</a>  <a id="10500" class="Symbol">:</a> <a id="10502" class="Symbol">∀</a> <a id="10504" class="Symbol">{</a><a id="10505" href="plfa.part1.Quantifiers.html#10505" class="Bound">n</a> <a id="10507" class="Symbol">:</a> <a id="10509" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10510" class="Symbol">}</a> <a id="10512" class="Symbol">→</a>  <a id="10515" href="plfa.part1.Quantifiers.html#9603" class="Datatype">odd</a> <a id="10519" href="plfa.part1.Quantifiers.html#10505" class="Bound">n</a> <a id="10521" class="Symbol">→</a> <a id="10523" href="plfa.part1.Quantifiers.html#7302" class="Function">∃[</a> <a id="10526" href="plfa.part1.Quantifiers.html#10526" class="Bound">m</a> <a id="10528" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="10530" class="Symbol">(</a><a id="10531" class="Number">1</a> <a id="10533" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="10535" href="plfa.part1.Quantifiers.html#10526" class="Bound">m</a> <a id="10537" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="10539" class="Number">2</a> <a id="10541" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10543" href="plfa.part1.Quantifiers.html#10505" class="Bound">n</a><a id="10544" class="Symbol">)</a>

<a id="10547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10440" class="Function">even-∃</a> <a id="10554" href="plfa.part1.Quantifiers.html#9638" class="InductiveConstructor">even-zero</a>                       <a id="10586" class="Symbol">=</a>  <a id="10589" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="10591" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="10596" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="10598" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10603" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a>
<a id="10605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10440" class="Function">even-∃</a> <a id="10612" class="Symbol">(</a><a id="10613" href="plfa.part1.Quantifiers.html#9663" class="InductiveConstructor">even-suc</a> <a id="10622" href="plfa.part1.Quantifiers.html#10622" class="Bound">o</a><a id="10623" class="Symbol">)</a> <a id="10625" class="Keyword">with</a> <a id="10630" href="plfa.part1.Quantifiers.html#10493" class="Function">odd-∃</a> <a id="10636" href="plfa.part1.Quantifiers.html#10622" class="Bound">o</a>
<a id="10638" class="Symbol">...</a>                    <a id="10661" class="Symbol">|</a> <a id="10663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4921" class="InductiveConstructor Operator">⟨</a> <a id="10665" href="plfa.part1.Quantifiers.html#10665" class="Bound">m</a> <a id="10667" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="10669" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10674" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a>  <a id="10677" class="Symbol">=</a>  <a id="10680" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="10682" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10686" href="plfa.part1.Quantifiers.html#10665" class="Bound">m</a> <a id="10688" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="10690" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10695" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a>

<a id="10698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10493" class="Function">odd-∃</a>  <a id="10705" class="Symbol">(</a><a id="10706" href="plfa.part1.Quantifiers.html#9752" class="InductiveConstructor">odd-suc</a> <a id="10714" href="plfa.part1.Quantifiers.html#10714" class="Bound">e</a><a id="10715" class="Symbol">)</a>  <a id="10718" class="Keyword">with</a> <a id="10723" href="plfa.part1.Quantifiers.html#10440" class="Function">even-∃</a> <a id="10730" href="plfa.part1.Quantifiers.html#10714" class="Bound">e</a>
<a id="10732" class="Symbol">...</a>                    <a id="10755" class="Symbol">|</a> <a id="10757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4921" class="InductiveConstructor Operator">⟨</a> <a id="10759" href="plfa.part1.Quantifiers.html#10759" class="Bound">m</a> <a id="10761" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="10763" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10768" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a>  <a id="10771" class="Symbol">=</a>  <a id="10774" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="10776" href="plfa.part1.Quantifiers.html#10759" class="Bound">m</a> <a id="10778" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="10780" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10785" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a>
</pre>{% endraw %}We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:

* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction:
{% raw %}<pre class="Agda"><a id="∃-even"></a><a id="11805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11805" class="Function">∃-even</a> <a id="11812" class="Symbol">:</a> <a id="11814" class="Symbol">∀</a> <a id="11816" class="Symbol">{</a><a id="11817" href="plfa.part1.Quantifiers.html#11817" class="Bound">n</a> <a id="11819" class="Symbol">:</a> <a id="11821" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11822" class="Symbol">}</a> <a id="11824" class="Symbol">→</a> <a id="11826" href="plfa.part1.Quantifiers.html#7302" class="Function">∃[</a> <a id="11829" href="plfa.part1.Quantifiers.html#11829" class="Bound">m</a> <a id="11831" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="11833" class="Symbol">(</a>    <a id="11838" href="plfa.part1.Quantifiers.html#11829" class="Bound">m</a> <a id="11840" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11842" class="Number">2</a> <a id="11844" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11846" href="plfa.part1.Quantifiers.html#11817" class="Bound">n</a><a id="11847" class="Symbol">)</a> <a id="11849" class="Symbol">→</a> <a id="11851" href="plfa.part1.Quantifiers.html#9583" class="Datatype">even</a> <a id="11856" href="plfa.part1.Quantifiers.html#11817" class="Bound">n</a>
<a id="∃-odd"></a><a id="11858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11858" class="Function">∃-odd</a>  <a id="11865" class="Symbol">:</a> <a id="11867" class="Symbol">∀</a> <a id="11869" class="Symbol">{</a><a id="11870" href="plfa.part1.Quantifiers.html#11870" class="Bound">n</a> <a id="11872" class="Symbol">:</a> <a id="11874" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11875" class="Symbol">}</a> <a id="11877" class="Symbol">→</a> <a id="11879" href="plfa.part1.Quantifiers.html#7302" class="Function">∃[</a> <a id="11882" href="plfa.part1.Quantifiers.html#11882" class="Bound">m</a> <a id="11884" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="11886" class="Symbol">(</a><a id="11887" class="Number">1</a> <a id="11889" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11891" href="plfa.part1.Quantifiers.html#11882" class="Bound">m</a> <a id="11893" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11895" class="Number">2</a> <a id="11897" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11899" href="plfa.part1.Quantifiers.html#11870" class="Bound">n</a><a id="11900" class="Symbol">)</a> <a id="11902" class="Symbol">→</a>  <a id="11905" href="plfa.part1.Quantifiers.html#9603" class="Datatype">odd</a> <a id="11909" href="plfa.part1.Quantifiers.html#11870" class="Bound">n</a>

<a id="11912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11805" class="Function">∃-even</a> <a id="11919" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a>  <a id="11922" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11927" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="11929" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11934" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a>  <a id="11937" class="Symbol">=</a>  <a id="11940" href="plfa.part1.Quantifiers.html#9638" class="InductiveConstructor">even-zero</a>
<a id="11950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11805" class="Function">∃-even</a> <a id="11957" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="11959" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11963" href="plfa.part1.Quantifiers.html#11963" class="Bound">m</a> <a id="11965" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="11967" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11972" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a>  <a id="11975" class="Symbol">=</a>  <a id="11978" href="plfa.part1.Quantifiers.html#9663" class="InductiveConstructor">even-suc</a> <a id="11987" class="Symbol">(</a><a id="11988" href="plfa.part1.Quantifiers.html#11858" class="Function">∃-odd</a> <a id="11994" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="11996" href="plfa.part1.Quantifiers.html#11963" class="Bound">m</a> <a id="11998" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="12000" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12005" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a><a id="12006" class="Symbol">)</a>

<a id="12009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11858" class="Function">∃-odd</a>  <a id="12016" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a>     <a id="12022" href="plfa.part1.Quantifiers.html#12022" class="Bound">m</a> <a id="12024" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="12026" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12031" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a>  <a id="12034" class="Symbol">=</a>  <a id="12037" href="plfa.part1.Quantifiers.html#9752" class="InductiveConstructor">odd-suc</a> <a id="12045" class="Symbol">(</a><a id="12046" href="plfa.part1.Quantifiers.html#11805" class="Function">∃-even</a> <a id="12053" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="12055" href="plfa.part1.Quantifiers.html#12022" class="Bound">m</a> <a id="12057" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="12059" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12064" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a><a id="12065" class="Symbol">)</a>
</pre>{% endraw %}Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:

- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.

This completes the proof in the backward direction.

#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

{% raw %}<pre class="Agda"><a id="13070" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

{% raw %}<pre class="Agda"><a id="13218" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{% raw %}<pre class="Agda"><a id="¬∃≃∀¬"></a><a id="13597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13597" class="Function">¬∃≃∀¬</a> <a id="13603" class="Symbol">:</a> <a id="13605" class="Symbol">∀</a> <a id="13607" class="Symbol">{</a><a id="13608" href="plfa.part1.Quantifiers.html#13608" class="Bound">A</a> <a id="13610" class="Symbol">:</a> <a id="13612" class="PrimitiveType">Set</a><a id="13615" class="Symbol">}</a> <a id="13617" class="Symbol">{</a><a id="13618" href="plfa.part1.Quantifiers.html#13618" class="Bound">B</a> <a id="13620" class="Symbol">:</a> <a id="13622" href="plfa.part1.Quantifiers.html#13608" class="Bound">A</a> <a id="13624" class="Symbol">→</a> <a id="13626" class="PrimitiveType">Set</a><a id="13629" class="Symbol">}</a>
  <a id="13633" class="Symbol">→</a> <a id="13635" class="Symbol">(</a><a id="13636" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7302" class="Function">∃[</a> <a id="13641" href="plfa.part1.Quantifiers.html#13641" class="Bound">x</a> <a id="13643" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="13645" href="plfa.part1.Quantifiers.html#13618" class="Bound">B</a> <a id="13647" href="plfa.part1.Quantifiers.html#13641" class="Bound">x</a><a id="13648" class="Symbol">)</a> <a id="13650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="13652" class="Symbol">∀</a> <a id="13654" href="plfa.part1.Quantifiers.html#13654" class="Bound">x</a> <a id="13656" class="Symbol">→</a> <a id="13658" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13660" href="plfa.part1.Quantifiers.html#13618" class="Bound">B</a> <a id="13662" href="plfa.part1.Quantifiers.html#13654" class="Bound">x</a>
<a id="13664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13597" class="Function">¬∃≃∀¬</a> <a id="13670" class="Symbol">=</a>
  <a id="13674" class="Keyword">record</a>
    <a id="13685" class="Symbol">{</a> <a id="13687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="13695" class="Symbol">=</a>  <a id="13698" class="Symbol">λ{</a> <a id="13701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13701" class="Bound">¬∃xy</a> <a id="13706" href="plfa.part1.Quantifiers.html#13706" class="Bound">x</a> <a id="13708" href="plfa.part1.Quantifiers.html#13708" class="Bound">y</a> <a id="13710" class="Symbol">→</a> <a id="13712" href="plfa.part1.Quantifiers.html#13701" class="Bound">¬∃xy</a> <a id="13717" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="13719" href="plfa.part1.Quantifiers.html#13706" class="Bound">x</a> <a id="13721" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="13723" href="plfa.part1.Quantifiers.html#13708" class="Bound">y</a> <a id="13725" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a> <a id="13727" class="Symbol">}</a>
    <a id="13733" class="Symbol">;</a> <a id="13735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="13743" class="Symbol">=</a>  <a id="13746" class="Symbol">λ{</a> <a id="13749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13749" class="Bound">∀¬xy</a> <a id="13754" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="13756" href="plfa.part1.Quantifiers.html#13756" class="Bound">x</a> <a id="13758" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="13760" href="plfa.part1.Quantifiers.html#13760" class="Bound">y</a> <a id="13762" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a> <a id="13764" class="Symbol">→</a> <a id="13766" href="plfa.part1.Quantifiers.html#13749" class="Bound">∀¬xy</a> <a id="13771" href="plfa.part1.Quantifiers.html#13756" class="Bound">x</a> <a id="13773" href="plfa.part1.Quantifiers.html#13760" class="Bound">y</a> <a id="13775" class="Symbol">}</a>
    <a id="13781" class="Symbol">;</a> <a id="13783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="13791" class="Symbol">=</a>  <a id="13794" class="Symbol">λ{</a> <a id="13797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13797" class="Bound">¬∃xy</a> <a id="13802" class="Symbol">→</a> <a id="13804" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="13819" class="Symbol">λ{</a> <a id="13822" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟨</a> <a id="13824" href="plfa.part1.Quantifiers.html#13824" class="Bound">x</a> <a id="13826" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">,</a> <a id="13828" href="plfa.part1.Quantifiers.html#13828" class="Bound">y</a> <a id="13830" href="plfa.part1.Quantifiers.html#4921" class="InductiveConstructor Operator">⟩</a> <a id="13832" class="Symbol">→</a> <a id="13834" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13839" class="Symbol">}</a> <a id="13841" class="Symbol">}</a>
    <a id="13847" class="Symbol">;</a> <a id="13849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="13857" class="Symbol">=</a>  <a id="13860" class="Symbol">λ{</a> <a id="13863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13863" class="Bound">∀¬xy</a> <a id="13868" class="Symbol">→</a> <a id="13870" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13875" class="Symbol">}</a>
    <a id="13881" class="Symbol">}</a>
</pre>{% endraw %}In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
{% raw %}<pre class="Agda"><a id="14698" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="14710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14710" class="Postulate">∃¬-implies-¬∀</a> <a id="14724" class="Symbol">:</a> <a id="14726" class="Symbol">∀</a> <a id="14728" class="Symbol">{</a><a id="14729" href="plfa.part1.Quantifiers.html#14729" class="Bound">A</a> <a id="14731" class="Symbol">:</a> <a id="14733" class="PrimitiveType">Set</a><a id="14736" class="Symbol">}</a> <a id="14738" class="Symbol">{</a><a id="14739" href="plfa.part1.Quantifiers.html#14739" class="Bound">B</a> <a id="14741" class="Symbol">:</a> <a id="14743" href="plfa.part1.Quantifiers.html#14729" class="Bound">A</a> <a id="14745" class="Symbol">→</a> <a id="14747" class="PrimitiveType">Set</a><a id="14750" class="Symbol">}</a>
    <a id="14756" class="Symbol">→</a> <a id="14758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7302" class="Function">∃[</a> <a id="14761" href="plfa.part1.Quantifiers.html#14761" class="Bound">x</a> <a id="14763" href="plfa.part1.Quantifiers.html#7302" class="Function">]</a> <a id="14765" class="Symbol">(</a><a id="14766" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14768" href="plfa.part1.Quantifiers.html#14739" class="Bound">B</a> <a id="14770" href="plfa.part1.Quantifiers.html#14761" class="Bound">x</a><a id="14771" class="Symbol">)</a>
      <a id="14779" class="Comment">--------------</a>
    <a id="14798" class="Symbol">→</a> <a id="14800" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14802" class="Symbol">(∀</a> <a id="14805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14805" class="Bound">x</a> <a id="14807" class="Symbol">→</a> <a id="14809" href="plfa.part1.Quantifiers.html#14739" class="Bound">B</a> <a id="14811" href="plfa.part1.Quantifiers.html#14805" class="Bound">x</a><a id="14812" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin),
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws), and
[Bin-predicates]({{ site.baseurl }}/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ](Can b)`.

We recommend proving the following lemmas which show that, for a given
binary number `b`, there is only one proof of `One b` and similarly
for `Can b`.

    ≡One : ∀{b : Bin} (o o' : One b) → o ≡ o'
    
    ≡Can : ∀{b : Bin} (cb : Can b) (cb' : Can b) → cb ≡ cb'

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {cb cb′ : ∃[ b ](Can b)} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′

{% raw %}<pre class="Agda"><a id="16076" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="16213" class="Keyword">import</a> <a id="16220" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="16233" class="Keyword">using</a> <a id="16239" class="Symbol">(</a><a id="16240" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="16241" class="Symbol">;</a> <a id="16243" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="16246" class="Symbol">;</a> <a id="16248" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="16249" class="Symbol">;</a> <a id="16251" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="16259" class="Symbol">;</a> <a id="16261" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="16269" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)