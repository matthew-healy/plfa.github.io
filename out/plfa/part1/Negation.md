---
src       : "src/plfa/part1/Negation.lagda.md"
title     : "Negation: Negation, with intuitionistic and classical logic"
layout    : page
prev      : /Connectives/
permalink : /Negation/
next      : /Quantifiers/
---

{% raw %}<pre class="Agda"><a id="180" class="Keyword">module</a> <a id="187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}" class="Module">plfa.part1.Negation</a> <a id="207" class="Keyword">where</a>
</pre>{% endraw %}
This chapter introduces negation, and discusses intuitionistic
and classical logic.

## Imports

{% raw %}<pre class="Agda"><a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="369" class="Keyword">using</a> <a id="375" class="Symbol">(</a><a id="376" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="379" class="Symbol">;</a> <a id="381" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="385" class="Symbol">)</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="408" class="Keyword">using</a> <a id="414" class="Symbol">(</a><a id="415" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="416" class="Symbol">;</a> <a id="418" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="422" class="Symbol">;</a> <a id="424" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="427" class="Symbol">)</a>
<a id="429" class="Keyword">open</a> <a id="434" class="Keyword">import</a> <a id="441" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="452" class="Keyword">using</a> <a id="458" class="Symbol">(</a><a id="459" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="460" class="Symbol">;</a> <a id="462" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="468" class="Symbol">)</a>
<a id="470" class="Keyword">open</a> <a id="475" class="Keyword">import</a> <a id="482" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="491" class="Keyword">using</a> <a id="497" class="Symbol">(</a><a id="498" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="501" class="Symbol">;</a> <a id="503" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="507" class="Symbol">;</a> <a id="509" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="513" class="Symbol">)</a>
<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="540" class="Keyword">using</a> <a id="546" class="Symbol">(</a><a id="547" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="550" class="Symbol">)</a>
<a id="552" class="Keyword">open</a> <a id="557" class="Keyword">import</a> <a id="564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="587" class="Keyword">using</a> <a id="593" class="Symbol">(</a><a id="594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">_≃_</a><a id="597" class="Symbol">;</a> <a id="599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#2684" class="Postulate">extensionality</a><a id="613" class="Symbol">)</a>
</pre>{% endraw %}

## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false:
{% raw %}<pre class="Agda"><a id="¬_"></a><a id="793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬_</a> <a id="796" class="Symbol">:</a> <a id="798" class="PrimitiveType">Set</a> <a id="802" class="Symbol">→</a> <a id="804" class="PrimitiveType">Set</a>
<a id="808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#810" class="Bound">A</a> <a id="812" class="Symbol">=</a> <a id="814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#810" class="Bound">A</a> <a id="816" class="Symbol">→</a> <a id="818" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}This is a form of _proof by contradiction_: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ{ x → N }

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction:
{% raw %}<pre class="Agda"><a id="¬-elim"></a><a id="1374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1374" class="Function">¬-elim</a> <a id="1381" class="Symbol">:</a> <a id="1383" class="Symbol">∀</a> <a id="1385" class="Symbol">{</a><a id="1386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1386" class="Bound">A</a> <a id="1388" class="Symbol">:</a> <a id="1390" class="PrimitiveType">Set</a><a id="1393" class="Symbol">}</a>
  <a id="1397" class="Symbol">→</a> <a id="1399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="1401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1386" class="Bound">A</a>
  <a id="1405" class="Symbol">→</a> <a id="1407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1386" class="Bound">A</a>
    <a id="1413" class="Comment">---</a>
  <a id="1419" class="Symbol">→</a> <a id="1421" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
<a id="1423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1374" class="Function">¬-elim</a> <a id="1430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1430" class="Bound">¬x</a> <a id="1433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1433" class="Bound">x</a> <a id="1435" class="Symbol">=</a> <a id="1437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1430" class="Bound">¬x</a> <a id="1440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1433" class="Bound">x</a>
</pre>{% endraw %}Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else:
{% raw %}<pre class="Agda"><a id="1825" class="Keyword">infix</a> <a id="1831" class="Number">3</a> <a id="1833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬_</a>
</pre>{% endraw %}Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.

In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`:
{% raw %}<pre class="Agda"><a id="¬¬-intro"></a><a id="2122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2122" class="Function">¬¬-intro</a> <a id="2131" class="Symbol">:</a> <a id="2133" class="Symbol">∀</a> <a id="2135" class="Symbol">{</a><a id="2136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2136" class="Bound">A</a> <a id="2138" class="Symbol">:</a> <a id="2140" class="PrimitiveType">Set</a><a id="2143" class="Symbol">}</a>
  <a id="2147" class="Symbol">→</a> <a id="2149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2136" class="Bound">A</a>
    <a id="2155" class="Comment">-----</a>
  <a id="2163" class="Symbol">→</a> <a id="2165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2136" class="Bound">A</a>
<a id="2171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2122" class="Function">¬¬-intro</a> <a id="2180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2180" class="Bound">x</a>  <a id="2183" class="Symbol">=</a>  <a id="2186" class="Symbol">λ{</a><a id="2188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2188" class="Bound">¬x</a> <a id="2191" class="Symbol">→</a> <a id="2193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2188" class="Bound">¬x</a> <a id="2196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2180" class="Bound">x</a><a id="2197" class="Symbol">}</a>
</pre>{% endraw %}Let `x` be evidence of `A`. We show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.

An equivalent way to write the above is as follows:
{% raw %}<pre class="Agda"><a id="¬¬-intro′"></a><a id="2504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2504" class="Function">¬¬-intro′</a> <a id="2514" class="Symbol">:</a> <a id="2516" class="Symbol">∀</a> <a id="2518" class="Symbol">{</a><a id="2519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2519" class="Bound">A</a> <a id="2521" class="Symbol">:</a> <a id="2523" class="PrimitiveType">Set</a><a id="2526" class="Symbol">}</a>
  <a id="2530" class="Symbol">→</a> <a id="2532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2519" class="Bound">A</a>
    <a id="2538" class="Comment">-----</a>
  <a id="2546" class="Symbol">→</a> <a id="2548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2519" class="Bound">A</a>
<a id="2554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2504" class="Function">¬¬-intro′</a> <a id="2564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2564" class="Bound">x</a> <a id="2566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2566" class="Bound">¬x</a> <a id="2569" class="Symbol">=</a> <a id="2571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2566" class="Bound">¬x</a> <a id="2574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2564" class="Bound">x</a>
</pre>{% endraw %}Here we have simply converted the argument of the lambda term
to an additional argument of the function.  We will usually
use this latter style, as it is more compact.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`:
{% raw %}<pre class="Agda"><a id="¬¬¬-elim"></a><a id="2840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2840" class="Function">¬¬¬-elim</a> <a id="2849" class="Symbol">:</a> <a id="2851" class="Symbol">∀</a> <a id="2853" class="Symbol">{</a><a id="2854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2854" class="Bound">A</a> <a id="2856" class="Symbol">:</a> <a id="2858" class="PrimitiveType">Set</a><a id="2861" class="Symbol">}</a>
  <a id="2865" class="Symbol">→</a> <a id="2867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2854" class="Bound">A</a>
    <a id="2879" class="Comment">-------</a>
  <a id="2889" class="Symbol">→</a> <a id="2891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2854" class="Bound">A</a>
<a id="2895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2840" class="Function">¬¬¬-elim</a> <a id="2904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2904" class="Bound">¬¬¬x</a>  <a id="2910" class="Symbol">=</a>  <a id="2913" class="Symbol">λ</a> <a id="2915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2915" class="Bound">x</a> <a id="2917" class="Symbol">→</a> <a id="2919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2904" class="Bound">¬¬¬x</a> <a id="2924" class="Symbol">(</a><a id="2925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2122" class="Function">¬¬-intro</a> <a id="2934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2915" class="Bound">x</a><a id="2935" class="Symbol">)</a>
</pre>{% endraw %}Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.

Another law of logic is _contraposition_,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`:
{% raw %}<pre class="Agda"><a id="contraposition"></a><a id="3397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3397" class="Function">contraposition</a> <a id="3412" class="Symbol">:</a> <a id="3414" class="Symbol">∀</a> <a id="3416" class="Symbol">{</a><a id="3417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3417" class="Bound">A</a> <a id="3419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3419" class="Bound">B</a> <a id="3421" class="Symbol">:</a> <a id="3423" class="PrimitiveType">Set</a><a id="3426" class="Symbol">}</a>
  <a id="3430" class="Symbol">→</a> <a id="3432" class="Symbol">(</a><a id="3433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3417" class="Bound">A</a> <a id="3435" class="Symbol">→</a> <a id="3437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3419" class="Bound">B</a><a id="3438" class="Symbol">)</a>
    <a id="3444" class="Comment">-----------</a>
  <a id="3458" class="Symbol">→</a> <a id="3460" class="Symbol">(</a><a id="3461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="3463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3419" class="Bound">B</a> <a id="3465" class="Symbol">→</a> <a id="3467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="3469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3417" class="Bound">A</a><a id="3470" class="Symbol">)</a>
<a id="3472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3397" class="Function">contraposition</a> <a id="3487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3487" class="Bound">f</a> <a id="3489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3489" class="Bound">¬y</a> <a id="3492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3492" class="Bound">x</a> <a id="3494" class="Symbol">=</a> <a id="3496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3489" class="Bound">¬y</a> <a id="3499" class="Symbol">(</a><a id="3500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3487" class="Bound">f</a> <a id="3502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3492" class="Bound">x</a><a id="3503" class="Symbol">)</a>
</pre>{% endraw %}Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence `¬ A`
must hold. Let `x` be evidence of `A`.  Then from `A → B` and `A` we
may conclude `B`, evidenced by `f x`, and from `B` and `¬ B` we may
conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown `¬ A`.

Using negation, it is straightforward to define inequality:
{% raw %}<pre class="Agda"><a id="_≢_"></a><a id="3919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3919" class="Function Operator">_≢_</a> <a id="3923" class="Symbol">:</a> <a id="3925" class="Symbol">∀</a> <a id="3927" class="Symbol">{</a><a id="3928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3928" class="Bound">A</a> <a id="3930" class="Symbol">:</a> <a id="3932" class="PrimitiveType">Set</a><a id="3935" class="Symbol">}</a> <a id="3937" class="Symbol">→</a> <a id="3939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3928" class="Bound">A</a> <a id="3941" class="Symbol">→</a> <a id="3943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3928" class="Bound">A</a> <a id="3945" class="Symbol">→</a> <a id="3947" class="PrimitiveType">Set</a>
<a id="3951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3951" class="Bound">x</a> <a id="3953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3919" class="Function Operator">≢</a> <a id="3955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3955" class="Bound">y</a>  <a id="3958" class="Symbol">=</a>  <a id="3961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="3963" class="Symbol">(</a><a id="3964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3951" class="Bound">x</a> <a id="3966" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3955" class="Bound">y</a><a id="3969" class="Symbol">)</a>
</pre>{% endraw %}It is trivial to show distinct numbers are not equal:
{% raw %}<pre class="Agda"><a id="4033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4033" class="Function">_</a> <a id="4035" class="Symbol">:</a> <a id="4037" class="Number">1</a> <a id="4039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3919" class="Function Operator">≢</a> <a id="4041" class="Number">2</a>
<a id="4043" class="Symbol">_</a> <a id="4045" class="Symbol">=</a> <a id="4047" class="Symbol">λ()</a>
</pre>{% endraw %}This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number:
{% raw %}<pre class="Agda"><a id="peano"></a><a id="4440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4440" class="Function">peano</a> <a id="4446" class="Symbol">:</a> <a id="4448" class="Symbol">∀</a> <a id="4450" class="Symbol">{</a><a id="4451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4451" class="Bound">m</a> <a id="4453" class="Symbol">:</a> <a id="4455" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4456" class="Symbol">}</a> <a id="4458" class="Symbol">→</a> <a id="4460" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="4465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3919" class="Function Operator">≢</a> <a id="4467" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4451" class="Bound">m</a>
<a id="4473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4440" class="Function">peano</a> <a id="4479" class="Symbol">=</a> <a id="4481" class="Symbol">λ()</a>
</pre>{% endraw %}The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.  We can write
this proof two different ways:
{% raw %}<pre class="Agda"><a id="id"></a><a id="4967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4967" class="Function">id</a> <a id="4970" class="Symbol">:</a> <a id="4972" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a> <a id="4974" class="Symbol">→</a> <a id="4976" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
<a id="4978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4967" class="Function">id</a> <a id="4981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4981" class="Bound">x</a> <a id="4983" class="Symbol">=</a> <a id="4985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4981" class="Bound">x</a>

<a id="id′"></a><a id="4988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4988" class="Function">id′</a> <a id="4992" class="Symbol">:</a> <a id="4994" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a> <a id="4996" class="Symbol">→</a> <a id="4998" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
<a id="5000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4988" class="Function">id′</a> <a id="5004" class="Symbol">()</a>
</pre>{% endraw %}But, using extensionality, we can prove these equal:
{% raw %}<pre class="Agda"><a id="id≡id′"></a><a id="5068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5068" class="Function">id≡id′</a> <a id="5075" class="Symbol">:</a> <a id="5077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4967" class="Function">id</a> <a id="5080" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4988" class="Function">id′</a>
<a id="5086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5068" class="Function">id≡id′</a> <a id="5093" class="Symbol">=</a> <a id="5095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#2684" class="Postulate">extensionality</a> <a id="5110" class="Symbol">(λ())</a>
</pre>{% endraw %}By extensionality, `id ≡ id′` holds if for every
`x` in their domain we have `id x ≡ id′ x`. But there
is no `x` in their domain, so the equality holds trivially.

Indeed, we can show any two proofs of a negation are equal:
{% raw %}<pre class="Agda"><a id="assimilation"></a><a id="5348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5348" class="Function">assimilation</a> <a id="5361" class="Symbol">:</a> <a id="5363" class="Symbol">∀</a> <a id="5365" class="Symbol">{</a><a id="5366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5366" class="Bound">A</a> <a id="5368" class="Symbol">:</a> <a id="5370" class="PrimitiveType">Set</a><a id="5373" class="Symbol">}</a> <a id="5375" class="Symbol">(</a><a id="5376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5376" class="Bound">¬x</a> <a id="5379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5379" class="Bound">¬x′</a> <a id="5383" class="Symbol">:</a> <a id="5385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="5387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5366" class="Bound">A</a><a id="5388" class="Symbol">)</a> <a id="5390" class="Symbol">→</a> <a id="5392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5376" class="Bound">¬x</a> <a id="5395" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5379" class="Bound">¬x′</a>
<a id="5401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5348" class="Function">assimilation</a> <a id="5414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5414" class="Bound">¬x</a> <a id="5417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5417" class="Bound">¬x′</a> <a id="5421" class="Symbol">=</a> <a id="5423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#2684" class="Postulate">extensionality</a> <a id="5438" class="Symbol">(λ</a> <a id="5441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5441" class="Bound">x</a> <a id="5443" class="Symbol">→</a> <a id="5445" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="5452" class="Symbol">(</a><a id="5453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5414" class="Bound">¬x</a> <a id="5456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5441" class="Bound">x</a><a id="5457" class="Symbol">))</a>
</pre>{% endraw %}Evidence for `¬ A` implies that any evidence of `A`
immediately leads to a contradiction.  But extensionality
quantifies over all `x` such that `A` holds, hence any
such `x` immediately leads to a contradiction,
again causing the equality to hold trivially.


#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality]({{ site.baseurl }}/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

{% raw %}<pre class="Agda"><a id="5920" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `trichotomy` (practice)

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}/Relations/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

{% raw %}<pre class="Agda"><a id="6330" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

{% raw %}<pre class="Agda"><a id="6602" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?


## Intuitive and Classical logic

In Gilbert and Sullivan's _The Gondoliers_, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."

Logic comes in many varieties, and one distinction is between
_classical_ and _intuitionistic_. Intuitionists, concerned
by assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
_which_ of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded middle, which
asserts `A ⊎ ¬ A` for every `A`, since the law gives no clue as to
_which_ of `A` or `¬ A` holds. Heyting formalised a variant of
Hilbert's classical logic that captures the intuitionistic notion of
provability. In particular, the law of the excluded middle is provable
in Hilbert's logic, but not in Heyting's.  Further, if the law of the
excluded middle is added as an axiom to Heyting's logic, then it
becomes equivalent to Hilbert's.  Kolmogorov showed the two logics
were closely related: he gave a double-negation translation, such that
a formula is provable in classical logic if and only if its
translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)

## Excluded middle is irrefutable

The law of the excluded middle can be formulated as follows:
{% raw %}<pre class="Agda"><a id="9138" class="Keyword">postulate</a>
  <a id="em"></a><a id="9150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9150" class="Postulate">em</a> <a id="9153" class="Symbol">:</a> <a id="9155" class="Symbol">∀</a> <a id="9157" class="Symbol">{</a><a id="9158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9158" class="Bound">A</a> <a id="9160" class="Symbol">:</a> <a id="9162" class="PrimitiveType">Set</a><a id="9165" class="Symbol">}</a> <a id="9167" class="Symbol">→</a> <a id="9169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9158" class="Bound">A</a> <a id="9171" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="9173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="9175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9158" class="Bound">A</a>
</pre>{% endraw %}As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is _irrefutable_,
meaning that the negation of its negation is provable (and hence that
its negation is never provable):
{% raw %}<pre class="Agda"><a id="em-irrefutable"></a><a id="9419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9419" class="Function">em-irrefutable</a> <a id="9434" class="Symbol">:</a> <a id="9436" class="Symbol">∀</a> <a id="9438" class="Symbol">{</a><a id="9439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9439" class="Bound">A</a> <a id="9441" class="Symbol">:</a> <a id="9443" class="PrimitiveType">Set</a><a id="9446" class="Symbol">}</a> <a id="9448" class="Symbol">→</a> <a id="9450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="9452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="9454" class="Symbol">(</a><a id="9455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9439" class="Bound">A</a> <a id="9457" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="9459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="9461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9439" class="Bound">A</a><a id="9462" class="Symbol">)</a>
<a id="9464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9419" class="Function">em-irrefutable</a> <a id="9479" class="Symbol">=</a> <a id="9481" class="Symbol">λ</a> <a id="9483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9483" class="Bound">k</a> <a id="9485" class="Symbol">→</a> <a id="9487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9483" class="Bound">k</a> <a id="9489" class="Symbol">(</a><a id="9490" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="9495" class="Symbol">(λ</a> <a id="9498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9498" class="Bound">x</a> <a id="9500" class="Symbol">→</a> <a id="9502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9483" class="Bound">k</a> <a id="9504" class="Symbol">(</a><a id="9505" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="9510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9498" class="Bound">x</a><a id="9511" class="Symbol">)))</a>
</pre>{% endraw %}The best way to explain this code is to develop it interactively:

    em-irrefutable k = ?

Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that given a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly:

    em-irrefutable k = k ?

We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct:

    em-irrefutable k = k (inj₂ λ{ x → ? })

The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, the only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly:

    em-irrefutable k = k (inj₂ λ{ x → k ? })

This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct:

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

There are no holes left! This completes the proof.

The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)

Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."

The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.

The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?

"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."

The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.

"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"

The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."

And the devil handed back to the man the same valise that the man had
just handed to him.

(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003.)


#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

{% raw %}<pre class="Agda"><a id="12900" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="13043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13043" class="Function">Stable</a> <a id="13050" class="Symbol">:</a> <a id="13052" class="PrimitiveType">Set</a> <a id="13056" class="Symbol">→</a> <a id="13058" class="PrimitiveType">Set</a>
<a id="13062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13043" class="Function">Stable</a> <a id="13069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13069" class="Bound">A</a> <a id="13071" class="Symbol">=</a> <a id="13073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="13075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="13077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13069" class="Bound">A</a> <a id="13079" class="Symbol">→</a> <a id="13081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13069" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

{% raw %}<pre class="Agda"><a id="13192" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="13328" class="Keyword">import</a> <a id="13335" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="13352" class="Keyword">using</a> <a id="13358" class="Symbol">(</a><a id="13359" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="13361" class="Symbol">)</a>
<a id="13363" class="Keyword">import</a> <a id="13370" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="13396" class="Keyword">using</a> <a id="13402" class="Symbol">(</a><a id="13403" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="13417" class="Symbol">)</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
