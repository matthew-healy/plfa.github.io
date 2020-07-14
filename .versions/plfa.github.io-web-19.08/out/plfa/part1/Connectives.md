---
src       : "src/plfa/part1/Connectives.lagda.md"
title     : "Connectives: Conjunction, disjunction, and implication"
layout    : page
prev      : /Isomorphism/
permalink : /Connectives/
next      : /Negation/
---

{% raw %}<pre class="Agda"><a id="175" class="Keyword">module</a> <a id="182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}" class="Module">plfa.part1.Connectives</a> <a id="205" class="Keyword">where</a>
</pre>{% endraw %}
<!-- The ⊥ ⊎ A ≅ A exercise requires a (inj₁ ()) pattern,
     which the reader will not have seen. Restore this
     exercise, and possibly also associativity? Take the
     exercises from the final sections on distributivity
     and exponentials? -->

This chapter introduces the basic logical connectives, by observing a
correspondence between connectives of logic and data types, a
principle known as _Propositions as Types_:

  * _conjunction_ is _product_,
  * _disjunction_ is _sum_,
  * _true_ is _unit type_,
  * _false_ is _empty type_,
  * _implication_ is _function space_.


## Imports

{% raw %}<pre class="Agda"><a id="821" class="Keyword">import</a> <a id="828" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="866" class="Symbol">as</a> <a id="869" class="Module">Eq</a>
<a id="872" class="Keyword">open</a> <a id="877" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="880" class="Keyword">using</a> <a id="886" class="Symbol">(</a><a id="887" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="890" class="Symbol">;</a> <a id="892" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="896" class="Symbol">)</a>
<a id="898" class="Keyword">open</a> <a id="903" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="918" class="Keyword">open</a> <a id="923" class="Keyword">import</a> <a id="930" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="939" class="Keyword">using</a> <a id="945" class="Symbol">(</a><a id="946" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="947" class="Symbol">)</a>
<a id="949" class="Keyword">open</a> <a id="954" class="Keyword">import</a> <a id="961" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="970" class="Keyword">using</a> <a id="976" class="Symbol">(</a><a id="977" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="980" class="Symbol">)</a>
<a id="982" class="Keyword">open</a> <a id="987" class="Keyword">import</a> <a id="994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="1017" class="Keyword">using</a> <a id="1023" class="Symbol">(</a><a id="1024" href="plfa.part1.Isomorphism.html#4365" class="Record Operator">_≃_</a><a id="1027" class="Symbol">;</a> <a id="1029" href="plfa.part1.Isomorphism.html#9186" class="Record Operator">_≲_</a><a id="1032" class="Symbol">;</a> <a id="1034" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a><a id="1048" class="Symbol">)</a>
<a id="1050" class="Keyword">open</a> <a id="1055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#8421" class="Module">plfa.part1.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}

## Conjunction is product

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{% raw %}<pre class="Agda"><a id="1290" class="Keyword">data</a> <a id="_×_"></a><a id="1295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1295" class="Datatype Operator">_×_</a> <a id="1299" class="Symbol">(</a><a id="1300" href="plfa.part1.Connectives.html#1300" class="Bound">A</a> <a id="1302" href="plfa.part1.Connectives.html#1302" class="Bound">B</a> <a id="1304" class="Symbol">:</a> <a id="1306" class="PrimitiveType">Set</a><a id="1309" class="Symbol">)</a> <a id="1311" class="Symbol">:</a> <a id="1313" class="PrimitiveType">Set</a> <a id="1317" class="Keyword">where</a>

  <a id="_×_.⟨_,_⟩"></a><a id="1326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="1332" class="Symbol">:</a>
      <a id="1340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1300" class="Bound">A</a>
    <a id="1346" class="Symbol">→</a> <a id="1348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1302" class="Bound">B</a>
      <a id="1356" class="Comment">-----</a>
    <a id="1366" class="Symbol">→</a> <a id="1368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1300" class="Bound">A</a> <a id="1370" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="1372" href="plfa.part1.Connectives.html#1302" class="Bound">B</a>
</pre>{% endraw %}Evidence that `A × B` holds is of the form `⟨ M , N ⟩`, where `M`
provides evidence that `A` holds and `N` provides evidence that `B`
holds.

Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds:
{% raw %}<pre class="Agda"><a id="proj₁"></a><a id="1611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1611" class="Function">proj₁</a> <a id="1617" class="Symbol">:</a> <a id="1619" class="Symbol">∀</a> <a id="1621" class="Symbol">{</a><a id="1622" href="plfa.part1.Connectives.html#1622" class="Bound">A</a> <a id="1624" href="plfa.part1.Connectives.html#1624" class="Bound">B</a> <a id="1626" class="Symbol">:</a> <a id="1628" class="PrimitiveType">Set</a><a id="1631" class="Symbol">}</a>
  <a id="1635" class="Symbol">→</a> <a id="1637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1622" class="Bound">A</a> <a id="1639" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="1641" href="plfa.part1.Connectives.html#1624" class="Bound">B</a>
    <a id="1647" class="Comment">-----</a>
  <a id="1655" class="Symbol">→</a> <a id="1657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1622" class="Bound">A</a>
<a id="1659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1611" class="Function">proj₁</a> <a id="1665" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="1667" href="plfa.part1.Connectives.html#1667" class="Bound">x</a> <a id="1669" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="1671" href="plfa.part1.Connectives.html#1671" class="Bound">y</a> <a id="1673" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="1675" class="Symbol">=</a> <a id="1677" href="plfa.part1.Connectives.html#1667" class="Bound">x</a>

<a id="proj₂"></a><a id="1680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1680" class="Function">proj₂</a> <a id="1686" class="Symbol">:</a> <a id="1688" class="Symbol">∀</a> <a id="1690" class="Symbol">{</a><a id="1691" href="plfa.part1.Connectives.html#1691" class="Bound">A</a> <a id="1693" href="plfa.part1.Connectives.html#1693" class="Bound">B</a> <a id="1695" class="Symbol">:</a> <a id="1697" class="PrimitiveType">Set</a><a id="1700" class="Symbol">}</a>
  <a id="1704" class="Symbol">→</a> <a id="1706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1691" class="Bound">A</a> <a id="1708" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="1710" href="plfa.part1.Connectives.html#1693" class="Bound">B</a>
    <a id="1716" class="Comment">-----</a>
  <a id="1724" class="Symbol">→</a> <a id="1726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1693" class="Bound">B</a>
<a id="1728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1680" class="Function">proj₂</a> <a id="1734" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="1736" href="plfa.part1.Connectives.html#1736" class="Bound">x</a> <a id="1738" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="1740" href="plfa.part1.Connectives.html#1740" class="Bound">y</a> <a id="1742" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="1744" class="Symbol">=</a> <a id="1746" href="plfa.part1.Connectives.html#1740" class="Bound">y</a>
</pre>{% endraw %}If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.

Equivalently, we could also declare conjunction as a record type:
{% raw %}<pre class="Agda"><a id="1965" class="Keyword">record</a> <a id="_×′_"></a><a id="1972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1972" class="Record Operator">_×′_</a> <a id="1977" class="Symbol">(</a><a id="1978" href="plfa.part1.Connectives.html#1978" class="Bound">A</a> <a id="1980" href="plfa.part1.Connectives.html#1980" class="Bound">B</a> <a id="1982" class="Symbol">:</a> <a id="1984" class="PrimitiveType">Set</a><a id="1987" class="Symbol">)</a> <a id="1989" class="Symbol">:</a> <a id="1991" class="PrimitiveType">Set</a> <a id="1995" class="Keyword">where</a>
  <a id="2003" class="Keyword">field</a>
    <a id="_×′_.proj₁′"></a><a id="2013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2013" class="Field">proj₁′</a> <a id="2020" class="Symbol">:</a> <a id="2022" href="plfa.part1.Connectives.html#1978" class="Bound">A</a>
    <a id="_×′_.proj₂′"></a><a id="2028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#2028" class="Field">proj₂′</a> <a id="2035" class="Symbol">:</a> <a id="2037" href="plfa.part1.Connectives.html#1980" class="Bound">B</a>
<a id="2039" class="Keyword">open</a> <a id="2044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1972" class="Module Operator">_×′_</a>
</pre>{% endraw %}Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B`.

When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a _constructor_, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a _destructor_.
We may also refer to `proj₁` and `proj₂` as destructors, since they
play a similar role.

Other terminology refers to `⟨_,_⟩` as _introducing_ a conjunction, and
to `proj₁` and `proj₂` as _eliminating_ a conjunction; indeed, the
former is sometimes given the name `×-I` and the latter two the names
`×-E₁` and `×-E₂`.  As we read the rules from top to bottom,
introduction and elimination do what they say on the tin: the first
_introduces_ a formula for the connective, which appears in the
conclusion but not in the hypotheses; the second _eliminates_ a
formula for the connective, which appears in a hypothesis but not in
the conclusion. An introduction rule describes under what conditions
we say the connective holds---how to _define_ the connective. An
elimination rule describes what we may conclude when the connective
holds---how to _use_ the connective.

(The paragraph above was adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)

In this case, applying each destructor and reassembling the results with the
constructor is the identity over products:
{% raw %}<pre class="Agda"><a id="η-×"></a><a id="3562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#3562" class="Function">η-×</a> <a id="3566" class="Symbol">:</a> <a id="3568" class="Symbol">∀</a> <a id="3570" class="Symbol">{</a><a id="3571" href="plfa.part1.Connectives.html#3571" class="Bound">A</a> <a id="3573" href="plfa.part1.Connectives.html#3573" class="Bound">B</a> <a id="3575" class="Symbol">:</a> <a id="3577" class="PrimitiveType">Set</a><a id="3580" class="Symbol">}</a> <a id="3582" class="Symbol">(</a><a id="3583" href="plfa.part1.Connectives.html#3583" class="Bound">w</a> <a id="3585" class="Symbol">:</a> <a id="3587" href="plfa.part1.Connectives.html#3571" class="Bound">A</a> <a id="3589" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="3591" href="plfa.part1.Connectives.html#3573" class="Bound">B</a><a id="3592" class="Symbol">)</a> <a id="3594" class="Symbol">→</a> <a id="3596" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="3598" href="plfa.part1.Connectives.html#1611" class="Function">proj₁</a> <a id="3604" href="plfa.part1.Connectives.html#3583" class="Bound">w</a> <a id="3606" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="3608" href="plfa.part1.Connectives.html#1680" class="Function">proj₂</a> <a id="3614" href="plfa.part1.Connectives.html#3583" class="Bound">w</a> <a id="3616" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="3618" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3620" href="plfa.part1.Connectives.html#3583" class="Bound">w</a>
<a id="3622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#3562" class="Function">η-×</a> <a id="3626" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="3628" href="plfa.part1.Connectives.html#3628" class="Bound">x</a> <a id="3630" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="3632" href="plfa.part1.Connectives.html#3632" class="Bound">y</a> <a id="3634" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="3636" class="Symbol">=</a> <a id="3638" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the
propositional equality to simplify to the same term.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction:
{% raw %}<pre class="Agda"><a id="3921" class="Keyword">infixr</a> <a id="3928" class="Number">2</a> <a id="3930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1295" class="Datatype Operator">_×_</a>
</pre>{% endraw %}Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.

Given two types `A` and `B`, we refer to `A × B` as the
_product_ of `A` and `B`.  In set theory, it is also sometimes
called the _Cartesian product_, and in computing it corresponds
to a _record_ type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members:
{% raw %}<pre class="Agda"><a id="4478" class="Keyword">data</a> <a id="Bool"></a><a id="4483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4483" class="Datatype">Bool</a> <a id="4488" class="Symbol">:</a> <a id="4490" class="PrimitiveType">Set</a> <a id="4494" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="4502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4502" class="InductiveConstructor">true</a>  <a id="4508" class="Symbol">:</a> <a id="4510" href="plfa.part1.Connectives.html#4483" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="4517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4517" class="InductiveConstructor">false</a> <a id="4523" class="Symbol">:</a> <a id="4525" href="plfa.part1.Connectives.html#4483" class="Datatype">Bool</a>

<a id="4531" class="Keyword">data</a> <a id="Tri"></a><a id="4536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4536" class="Datatype">Tri</a> <a id="4540" class="Symbol">:</a> <a id="4542" class="PrimitiveType">Set</a> <a id="4546" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="4554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4554" class="InductiveConstructor">aa</a> <a id="4557" class="Symbol">:</a> <a id="4559" href="plfa.part1.Connectives.html#4536" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="4565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4565" class="InductiveConstructor">bb</a> <a id="4568" class="Symbol">:</a> <a id="4570" href="plfa.part1.Connectives.html#4536" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="4576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4576" class="InductiveConstructor">cc</a> <a id="4579" class="Symbol">:</a> <a id="4581" href="plfa.part1.Connectives.html#4536" class="Datatype">Tri</a>
</pre>{% endraw %}Then the type `Bool × Tri` has six members:

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
{% raw %}<pre class="Agda"><a id="×-count"></a><a id="4841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4841" class="Function">×-count</a> <a id="4849" class="Symbol">:</a> <a id="4851" href="plfa.part1.Connectives.html#4483" class="Datatype">Bool</a> <a id="4856" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="4858" href="plfa.part1.Connectives.html#4536" class="Datatype">Tri</a> <a id="4862" class="Symbol">→</a> <a id="4864" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="4866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4841" class="Function">×-count</a> <a id="4874" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="4876" href="plfa.part1.Connectives.html#4502" class="InductiveConstructor">true</a>  <a id="4882" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="4884" href="plfa.part1.Connectives.html#4554" class="InductiveConstructor">aa</a> <a id="4887" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>  <a id="4890" class="Symbol">=</a>  <a id="4893" class="Number">1</a>
<a id="4895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4841" class="Function">×-count</a> <a id="4903" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="4905" href="plfa.part1.Connectives.html#4502" class="InductiveConstructor">true</a>  <a id="4911" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="4913" href="plfa.part1.Connectives.html#4565" class="InductiveConstructor">bb</a> <a id="4916" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>  <a id="4919" class="Symbol">=</a>  <a id="4922" class="Number">2</a>
<a id="4924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4841" class="Function">×-count</a> <a id="4932" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="4934" href="plfa.part1.Connectives.html#4502" class="InductiveConstructor">true</a>  <a id="4940" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="4942" href="plfa.part1.Connectives.html#4576" class="InductiveConstructor">cc</a> <a id="4945" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>  <a id="4948" class="Symbol">=</a>  <a id="4951" class="Number">3</a>
<a id="4953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4841" class="Function">×-count</a> <a id="4961" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="4963" href="plfa.part1.Connectives.html#4517" class="InductiveConstructor">false</a> <a id="4969" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="4971" href="plfa.part1.Connectives.html#4554" class="InductiveConstructor">aa</a> <a id="4974" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>  <a id="4977" class="Symbol">=</a>  <a id="4980" class="Number">4</a>
<a id="4982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4841" class="Function">×-count</a> <a id="4990" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="4992" href="plfa.part1.Connectives.html#4517" class="InductiveConstructor">false</a> <a id="4998" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="5000" href="plfa.part1.Connectives.html#4565" class="InductiveConstructor">bb</a> <a id="5003" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>  <a id="5006" class="Symbol">=</a>  <a id="5009" class="Number">5</a>
<a id="5011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4841" class="Function">×-count</a> <a id="5019" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="5021" href="plfa.part1.Connectives.html#4517" class="InductiveConstructor">false</a> <a id="5027" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="5029" href="plfa.part1.Connectives.html#4576" class="InductiveConstructor">cc</a> <a id="5032" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>  <a id="5035" class="Symbol">=</a>  <a id="5038" class="Number">6</a>
</pre>{% endraw %}
Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative _up to
isomorphism_.

For commutativity, the `to` function swaps a pair, taking `⟨ x , y ⟩` to
`⟨ y , x ⟩`, and the `from` function does the same (up to renaming).
Instantiating the patterns correctly in `from∘to` and `to∘from` is essential.
Replacing the definition of `from∘to` by `λ w → refl` will not work;
and similarly for `to∘from`:
{% raw %}<pre class="Agda"><a id="×-comm"></a><a id="5577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#5577" class="Function">×-comm</a> <a id="5584" class="Symbol">:</a> <a id="5586" class="Symbol">∀</a> <a id="5588" class="Symbol">{</a><a id="5589" href="plfa.part1.Connectives.html#5589" class="Bound">A</a> <a id="5591" href="plfa.part1.Connectives.html#5591" class="Bound">B</a> <a id="5593" class="Symbol">:</a> <a id="5595" class="PrimitiveType">Set</a><a id="5598" class="Symbol">}</a> <a id="5600" class="Symbol">→</a> <a id="5602" href="plfa.part1.Connectives.html#5589" class="Bound">A</a> <a id="5604" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="5606" href="plfa.part1.Connectives.html#5591" class="Bound">B</a> <a id="5608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="5610" href="plfa.part1.Connectives.html#5591" class="Bound">B</a> <a id="5612" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="5614" href="plfa.part1.Connectives.html#5589" class="Bound">A</a>
<a id="5616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#5577" class="Function">×-comm</a> <a id="5623" class="Symbol">=</a>
  <a id="5627" class="Keyword">record</a>
    <a id="5638" class="Symbol">{</a> <a id="5640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>       <a id="5649" class="Symbol">=</a>  <a id="5652" class="Symbol">λ{</a> <a id="5655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="5657" href="plfa.part1.Connectives.html#5657" class="Bound">x</a> <a id="5659" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="5661" href="plfa.part1.Connectives.html#5661" class="Bound">y</a> <a id="5663" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="5665" class="Symbol">→</a> <a id="5667" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="5669" href="plfa.part1.Connectives.html#5661" class="Bound">y</a> <a id="5671" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="5673" href="plfa.part1.Connectives.html#5657" class="Bound">x</a> <a id="5675" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="5677" class="Symbol">}</a>
    <a id="5683" class="Symbol">;</a> <a id="5685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>     <a id="5694" class="Symbol">=</a>  <a id="5697" class="Symbol">λ{</a> <a id="5700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="5702" href="plfa.part1.Connectives.html#5702" class="Bound">y</a> <a id="5704" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="5706" href="plfa.part1.Connectives.html#5706" class="Bound">x</a> <a id="5708" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="5710" class="Symbol">→</a> <a id="5712" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="5714" href="plfa.part1.Connectives.html#5706" class="Bound">x</a> <a id="5716" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="5718" href="plfa.part1.Connectives.html#5702" class="Bound">y</a> <a id="5720" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="5722" class="Symbol">}</a>
    <a id="5728" class="Symbol">;</a> <a id="5730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a>  <a id="5739" class="Symbol">=</a>  <a id="5742" class="Symbol">λ{</a> <a id="5745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="5747" href="plfa.part1.Connectives.html#5747" class="Bound">x</a> <a id="5749" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="5751" href="plfa.part1.Connectives.html#5751" class="Bound">y</a> <a id="5753" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="5755" class="Symbol">→</a> <a id="5757" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="5762" class="Symbol">}</a>
    <a id="5768" class="Symbol">;</a> <a id="5770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a>  <a id="5779" class="Symbol">=</a>  <a id="5782" class="Symbol">λ{</a> <a id="5785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="5787" href="plfa.part1.Connectives.html#5787" class="Bound">y</a> <a id="5789" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="5791" href="plfa.part1.Connectives.html#5791" class="Bound">x</a> <a id="5793" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="5795" class="Symbol">→</a> <a id="5797" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="5802" class="Symbol">}</a>
    <a id="5808" class="Symbol">}</a>
</pre>{% endraw %}
Being _commutative_ is different from being _commutative up to
isomorphism_.  Compare the two statements:

    m * n ≡ n * m
    A × B ≃ B × A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
_not_ the same as `Tri × Bool`.  But there is an isomorphism between
the two types.  For instance, `⟨ true , aa ⟩`, which is a member of the
former, corresponds to `⟨ aa , true ⟩`, which is a member of the latter.

For associativity, the `to` function reassociates two uses of pairing,
taking `⟨ ⟨ x , y ⟩ , z ⟩` to `⟨ x , ⟨ y , z ⟩ ⟩`, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification:
{% raw %}<pre class="Agda"><a id="×-assoc"></a><a id="6664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6664" class="Function">×-assoc</a> <a id="6672" class="Symbol">:</a> <a id="6674" class="Symbol">∀</a> <a id="6676" class="Symbol">{</a><a id="6677" href="plfa.part1.Connectives.html#6677" class="Bound">A</a> <a id="6679" href="plfa.part1.Connectives.html#6679" class="Bound">B</a> <a id="6681" href="plfa.part1.Connectives.html#6681" class="Bound">C</a> <a id="6683" class="Symbol">:</a> <a id="6685" class="PrimitiveType">Set</a><a id="6688" class="Symbol">}</a> <a id="6690" class="Symbol">→</a> <a id="6692" class="Symbol">(</a><a id="6693" href="plfa.part1.Connectives.html#6677" class="Bound">A</a> <a id="6695" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="6697" href="plfa.part1.Connectives.html#6679" class="Bound">B</a><a id="6698" class="Symbol">)</a> <a id="6700" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="6702" href="plfa.part1.Connectives.html#6681" class="Bound">C</a> <a id="6704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="6706" href="plfa.part1.Connectives.html#6677" class="Bound">A</a> <a id="6708" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="6710" class="Symbol">(</a><a id="6711" href="plfa.part1.Connectives.html#6679" class="Bound">B</a> <a id="6713" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="6715" href="plfa.part1.Connectives.html#6681" class="Bound">C</a><a id="6716" class="Symbol">)</a>
<a id="6718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#6664" class="Function">×-assoc</a> <a id="6726" class="Symbol">=</a>
  <a id="6730" class="Keyword">record</a>
    <a id="6741" class="Symbol">{</a> <a id="6743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="6751" class="Symbol">=</a> <a id="6753" class="Symbol">λ{</a> <a id="6756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="6758" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="6760" href="plfa.part1.Connectives.html#6760" class="Bound">x</a> <a id="6762" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6764" href="plfa.part1.Connectives.html#6764" class="Bound">y</a> <a id="6766" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6768" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6770" href="plfa.part1.Connectives.html#6770" class="Bound">z</a> <a id="6772" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6774" class="Symbol">→</a> <a id="6776" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="6778" href="plfa.part1.Connectives.html#6760" class="Bound">x</a> <a id="6780" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6782" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="6784" href="plfa.part1.Connectives.html#6764" class="Bound">y</a> <a id="6786" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6788" href="plfa.part1.Connectives.html#6770" class="Bound">z</a> <a id="6790" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6792" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6794" class="Symbol">}</a>
    <a id="6800" class="Symbol">;</a> <a id="6802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="6810" class="Symbol">=</a> <a id="6812" class="Symbol">λ{</a> <a id="6815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="6817" href="plfa.part1.Connectives.html#6817" class="Bound">x</a> <a id="6819" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6821" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="6823" href="plfa.part1.Connectives.html#6823" class="Bound">y</a> <a id="6825" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6827" href="plfa.part1.Connectives.html#6827" class="Bound">z</a> <a id="6829" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6831" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6833" class="Symbol">→</a> <a id="6835" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="6837" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="6839" href="plfa.part1.Connectives.html#6817" class="Bound">x</a> <a id="6841" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6843" href="plfa.part1.Connectives.html#6823" class="Bound">y</a> <a id="6845" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6847" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6849" href="plfa.part1.Connectives.html#6827" class="Bound">z</a> <a id="6851" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6853" class="Symbol">}</a>
    <a id="6859" class="Symbol">;</a> <a id="6861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="6869" class="Symbol">=</a> <a id="6871" class="Symbol">λ{</a> <a id="6874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="6876" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="6878" href="plfa.part1.Connectives.html#6878" class="Bound">x</a> <a id="6880" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6882" href="plfa.part1.Connectives.html#6882" class="Bound">y</a> <a id="6884" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6886" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6888" href="plfa.part1.Connectives.html#6888" class="Bound">z</a> <a id="6890" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6892" class="Symbol">→</a> <a id="6894" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="6899" class="Symbol">}</a>
    <a id="6905" class="Symbol">;</a> <a id="6907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="6915" class="Symbol">=</a> <a id="6917" class="Symbol">λ{</a> <a id="6920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="6922" href="plfa.part1.Connectives.html#6922" class="Bound">x</a> <a id="6924" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6926" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="6928" href="plfa.part1.Connectives.html#6928" class="Bound">y</a> <a id="6930" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="6932" href="plfa.part1.Connectives.html#6932" class="Bound">z</a> <a id="6934" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6936" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="6938" class="Symbol">→</a> <a id="6940" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="6945" class="Symbol">}</a>
    <a id="6951" class="Symbol">}</a>
</pre>{% endraw %}
Being _associative_ is not the same as being _associative
up to isomorphism_.  Compare the two statements:

    (m * n) * p ≡ m * (n * p)
    (A × B) × C ≃ A × (B × C)

For example, the type `(ℕ × Bool) × Tri` is _not_ the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `⟨ ⟨ 1 , true ⟩ , aa ⟩`, which is a member of the former,
corresponds to `⟨ 1 , ⟨ true , aa ⟩ ⟩`, which is a member of the latter.

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier]({{ site.baseurl }}/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.

{% raw %}<pre class="Agda"><a id="7559" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Truth is unit

Truth `⊤` always holds. We formalise this idea by
declaring a suitable inductive type:
{% raw %}<pre class="Agda"><a id="7697" class="Keyword">data</a> <a id="⊤"></a><a id="7702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#7702" class="Datatype">⊤</a> <a id="7704" class="Symbol">:</a> <a id="7706" class="PrimitiveType">Set</a> <a id="7710" class="Keyword">where</a>

  <a id="⊤.tt"></a><a id="7719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#7719" class="InductiveConstructor">tt</a> <a id="7722" class="Symbol">:</a>
    <a id="7728" class="Comment">--</a>
    <a id="7735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#7702" class="Datatype">⊤</a>
</pre>{% endraw %}Evidence that `⊤` holds is of the form `tt`.

There is an introduction rule, but no elimination rule.
Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.

The nullary case of `η-×` is `η-⊤`, which asserts that any
value of type `⊤` must be equal to `tt`:
{% raw %}<pre class="Agda"><a id="η-⊤"></a><a id="8101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#8101" class="Function">η-⊤</a> <a id="8105" class="Symbol">:</a> <a id="8107" class="Symbol">∀</a> <a id="8109" class="Symbol">(</a><a id="8110" href="plfa.part1.Connectives.html#8110" class="Bound">w</a> <a id="8112" class="Symbol">:</a> <a id="8114" href="plfa.part1.Connectives.html#7702" class="Datatype">⊤</a><a id="8115" class="Symbol">)</a> <a id="8117" class="Symbol">→</a> <a id="8119" href="plfa.part1.Connectives.html#7719" class="InductiveConstructor">tt</a> <a id="8122" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8124" href="plfa.part1.Connectives.html#8110" class="Bound">w</a>
<a id="8126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#8101" class="Function">η-⊤</a> <a id="8130" href="plfa.part1.Connectives.html#7719" class="InductiveConstructor">tt</a> <a id="8133" class="Symbol">=</a> <a id="8135" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}The pattern matching on the left-hand side is essential.  Replacing
`w` by `tt` allows both sides of the propositional equality to
simplify to the same term.

We refer to `⊤` as the _unit_ type. And, indeed,
type `⊤` has exactly one member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:
{% raw %}<pre class="Agda"><a id="⊤-count"></a><a id="8479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#8479" class="Function">⊤-count</a> <a id="8487" class="Symbol">:</a> <a id="8489" href="plfa.part1.Connectives.html#7702" class="Datatype">⊤</a> <a id="8491" class="Symbol">→</a> <a id="8493" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="8495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#8479" class="Function">⊤-count</a> <a id="8503" href="plfa.part1.Connectives.html#7719" class="InductiveConstructor">tt</a> <a id="8506" class="Symbol">=</a> <a id="8508" class="Number">1</a>
</pre>{% endraw %}
For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product _up to isomorphism_.  For left
identity, the `to` function takes `⟨ tt , x ⟩` to `x`, and the `from`
function does the inverse.  The evidence of left inverse requires
matching against a suitable pattern to enable simplification:
{% raw %}<pre class="Agda"><a id="⊤-identityˡ"></a><a id="8849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#8849" class="Function">⊤-identityˡ</a> <a id="8861" class="Symbol">:</a> <a id="8863" class="Symbol">∀</a> <a id="8865" class="Symbol">{</a><a id="8866" href="plfa.part1.Connectives.html#8866" class="Bound">A</a> <a id="8868" class="Symbol">:</a> <a id="8870" class="PrimitiveType">Set</a><a id="8873" class="Symbol">}</a> <a id="8875" class="Symbol">→</a> <a id="8877" href="plfa.part1.Connectives.html#7702" class="Datatype">⊤</a> <a id="8879" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="8881" href="plfa.part1.Connectives.html#8866" class="Bound">A</a> <a id="8883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8885" href="plfa.part1.Connectives.html#8866" class="Bound">A</a>
<a id="8887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#8849" class="Function">⊤-identityˡ</a> <a id="8899" class="Symbol">=</a>
  <a id="8903" class="Keyword">record</a>
    <a id="8914" class="Symbol">{</a> <a id="8916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="8924" class="Symbol">=</a> <a id="8926" class="Symbol">λ{</a> <a id="8929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="8931" href="plfa.part1.Connectives.html#7719" class="InductiveConstructor">tt</a> <a id="8934" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="8936" href="plfa.part1.Connectives.html#8936" class="Bound">x</a> <a id="8938" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="8940" class="Symbol">→</a> <a id="8942" href="plfa.part1.Connectives.html#8936" class="Bound">x</a> <a id="8944" class="Symbol">}</a>
    <a id="8950" class="Symbol">;</a> <a id="8952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="8960" class="Symbol">=</a> <a id="8962" class="Symbol">λ{</a> <a id="8965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#8965" class="Bound">x</a> <a id="8967" class="Symbol">→</a> <a id="8969" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="8971" href="plfa.part1.Connectives.html#7719" class="InductiveConstructor">tt</a> <a id="8974" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="8976" href="plfa.part1.Connectives.html#8965" class="Bound">x</a> <a id="8978" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="8980" class="Symbol">}</a>
    <a id="8986" class="Symbol">;</a> <a id="8988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="8996" class="Symbol">=</a> <a id="8998" class="Symbol">λ{</a> <a id="9001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="9003" href="plfa.part1.Connectives.html#7719" class="InductiveConstructor">tt</a> <a id="9006" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="9008" href="plfa.part1.Connectives.html#9008" class="Bound">x</a> <a id="9010" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="9012" class="Symbol">→</a> <a id="9014" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9019" class="Symbol">}</a>
    <a id="9025" class="Symbol">;</a> <a id="9027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="9035" class="Symbol">=</a> <a id="9037" class="Symbol">λ{</a> <a id="9040" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#9040" class="Bound">x</a> <a id="9042" class="Symbol">→</a> <a id="9044" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9049" class="Symbol">}</a>
    <a id="9055" class="Symbol">}</a>
</pre>{% endraw %}
Having an _identity_ is different from having an identity
_up to isomorphism_.  Compare the two statements:

    1 * m ≡ m
    ⊤ × A ≃ A

In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is _not_ the
same as `Bool`.  But there is an isomorphism between the two types.
For instance, `⟨ tt , true ⟩`, which is a member of the former,
corresponds to `true`, which is a member of the latter.

Right identity follows from commutativity of product and left identity:
{% raw %}<pre class="Agda"><a id="⊤-identityʳ"></a><a id="9641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#9641" class="Function">⊤-identityʳ</a> <a id="9653" class="Symbol">:</a> <a id="9655" class="Symbol">∀</a> <a id="9657" class="Symbol">{</a><a id="9658" href="plfa.part1.Connectives.html#9658" class="Bound">A</a> <a id="9660" class="Symbol">:</a> <a id="9662" class="PrimitiveType">Set</a><a id="9665" class="Symbol">}</a> <a id="9667" class="Symbol">→</a> <a id="9669" class="Symbol">(</a><a id="9670" href="plfa.part1.Connectives.html#9658" class="Bound">A</a> <a id="9672" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="9674" href="plfa.part1.Connectives.html#7702" class="Datatype">⊤</a><a id="9675" class="Symbol">)</a> <a id="9677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="9679" href="plfa.part1.Connectives.html#9658" class="Bound">A</a>
<a id="9681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#9641" class="Function">⊤-identityʳ</a> <a id="9693" class="Symbol">{</a><a id="9694" href="plfa.part1.Connectives.html#9694" class="Bound">A</a><a id="9695" class="Symbol">}</a> <a id="9697" class="Symbol">=</a>
  <a id="9701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#8497" class="Function Operator">≃-begin</a>
    <a id="9713" class="Symbol">(</a><a id="9714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#9694" class="Bound">A</a> <a id="9716" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="9718" href="plfa.part1.Connectives.html#7702" class="Datatype">⊤</a><a id="9719" class="Symbol">)</a>
  <a id="9723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#8581" class="Function Operator">≃⟨</a> <a id="9726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#5577" class="Function">×-comm</a> <a id="9733" href="plfa.part1.Isomorphism.html#8581" class="Function Operator">⟩</a>
    <a id="9739" class="Symbol">(</a><a id="9740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#7702" class="Datatype">⊤</a> <a id="9742" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="9744" href="plfa.part1.Connectives.html#9694" class="Bound">A</a><a id="9745" class="Symbol">)</a>
  <a id="9749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#8581" class="Function Operator">≃⟨</a> <a id="9752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#8849" class="Function">⊤-identityˡ</a> <a id="9764" href="plfa.part1.Isomorphism.html#8581" class="Function Operator">⟩</a>
    <a id="9770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#9694" class="Bound">A</a>
  <a id="9774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#8700" class="Function Operator">≃-∎</a>
</pre>{% endraw %}Here we have used a chain of isomorphisms, analogous to that used for
equality.


## Disjunction is sum

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{% raw %}<pre class="Agda"><a id="10055" class="Keyword">data</a> <a id="_⊎_"></a><a id="10060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10060" class="Datatype Operator">_⊎_</a> <a id="10064" class="Symbol">(</a><a id="10065" href="plfa.part1.Connectives.html#10065" class="Bound">A</a> <a id="10067" href="plfa.part1.Connectives.html#10067" class="Bound">B</a> <a id="10069" class="Symbol">:</a> <a id="10071" class="PrimitiveType">Set</a><a id="10074" class="Symbol">)</a> <a id="10076" class="Symbol">:</a> <a id="10078" class="PrimitiveType">Set</a> <a id="10082" class="Keyword">where</a>

  <a id="_⊎_.inj₁"></a><a id="10091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10091" class="InductiveConstructor">inj₁</a> <a id="10096" class="Symbol">:</a>
      <a id="10104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10065" class="Bound">A</a>
      <a id="10112" class="Comment">-----</a>
    <a id="10122" class="Symbol">→</a> <a id="10124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10065" class="Bound">A</a> <a id="10126" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="10128" href="plfa.part1.Connectives.html#10067" class="Bound">B</a>

  <a id="_⊎_.inj₂"></a><a id="10133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10133" class="InductiveConstructor">inj₂</a> <a id="10138" class="Symbol">:</a>
      <a id="10146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10067" class="Bound">B</a>
      <a id="10154" class="Comment">-----</a>
    <a id="10164" class="Symbol">→</a> <a id="10166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10065" class="Bound">A</a> <a id="10168" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="10170" href="plfa.part1.Connectives.html#10067" class="Bound">B</a>
</pre>{% endraw %}Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds:
{% raw %}<pre class="Agda"><a id="case-⊎"></a><a id="10464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10464" class="Function">case-⊎</a> <a id="10471" class="Symbol">:</a> <a id="10473" class="Symbol">∀</a> <a id="10475" class="Symbol">{</a><a id="10476" href="plfa.part1.Connectives.html#10476" class="Bound">A</a> <a id="10478" href="plfa.part1.Connectives.html#10478" class="Bound">B</a> <a id="10480" href="plfa.part1.Connectives.html#10480" class="Bound">C</a> <a id="10482" class="Symbol">:</a> <a id="10484" class="PrimitiveType">Set</a><a id="10487" class="Symbol">}</a>
  <a id="10491" class="Symbol">→</a> <a id="10493" class="Symbol">(</a><a id="10494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10476" class="Bound">A</a> <a id="10496" class="Symbol">→</a> <a id="10498" href="plfa.part1.Connectives.html#10480" class="Bound">C</a><a id="10499" class="Symbol">)</a>
  <a id="10503" class="Symbol">→</a> <a id="10505" class="Symbol">(</a><a id="10506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10478" class="Bound">B</a> <a id="10508" class="Symbol">→</a> <a id="10510" href="plfa.part1.Connectives.html#10480" class="Bound">C</a><a id="10511" class="Symbol">)</a>
  <a id="10515" class="Symbol">→</a> <a id="10517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10476" class="Bound">A</a> <a id="10519" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="10521" href="plfa.part1.Connectives.html#10478" class="Bound">B</a>
    <a id="10527" class="Comment">-----------</a>
  <a id="10541" class="Symbol">→</a> <a id="10543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10480" class="Bound">C</a>
<a id="10545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10464" class="Function">case-⊎</a> <a id="10552" href="plfa.part1.Connectives.html#10552" class="Bound">f</a> <a id="10554" href="plfa.part1.Connectives.html#10554" class="Bound">g</a> <a id="10556" class="Symbol">(</a><a id="10557" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="10562" href="plfa.part1.Connectives.html#10562" class="Bound">x</a><a id="10563" class="Symbol">)</a> <a id="10565" class="Symbol">=</a> <a id="10567" href="plfa.part1.Connectives.html#10552" class="Bound">f</a> <a id="10569" href="plfa.part1.Connectives.html#10562" class="Bound">x</a>
<a id="10571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10464" class="Function">case-⊎</a> <a id="10578" href="plfa.part1.Connectives.html#10578" class="Bound">f</a> <a id="10580" href="plfa.part1.Connectives.html#10580" class="Bound">g</a> <a id="10582" class="Symbol">(</a><a id="10583" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="10588" href="plfa.part1.Connectives.html#10588" class="Bound">y</a><a id="10589" class="Symbol">)</a> <a id="10591" class="Symbol">=</a> <a id="10593" href="plfa.part1.Connectives.html#10580" class="Bound">g</a> <a id="10595" href="plfa.part1.Connectives.html#10588" class="Bound">y</a>
</pre>{% endraw %}Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as _constructors_, and when they appear on the
left-hand side we refer to them as _destructors_.  We also refer to
`case-⊎` as a destructor, since it plays a similar role.  Other
terminology refers to `inj₁` and `inj₂` as _introducing_ a
disjunction, and to `case-⊎` as _eliminating_ a disjunction; indeed
the former are sometimes given the names `⊎-I₁` and `⊎-I₂` and the
latter the name `⊎-E`.

Applying the destructor to each of the constructors is the identity:
{% raw %}<pre class="Agda"><a id="η-⊎"></a><a id="11264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11264" class="Function">η-⊎</a> <a id="11268" class="Symbol">:</a> <a id="11270" class="Symbol">∀</a> <a id="11272" class="Symbol">{</a><a id="11273" href="plfa.part1.Connectives.html#11273" class="Bound">A</a> <a id="11275" href="plfa.part1.Connectives.html#11275" class="Bound">B</a> <a id="11277" class="Symbol">:</a> <a id="11279" class="PrimitiveType">Set</a><a id="11282" class="Symbol">}</a> <a id="11284" class="Symbol">(</a><a id="11285" href="plfa.part1.Connectives.html#11285" class="Bound">w</a> <a id="11287" class="Symbol">:</a> <a id="11289" href="plfa.part1.Connectives.html#11273" class="Bound">A</a> <a id="11291" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="11293" href="plfa.part1.Connectives.html#11275" class="Bound">B</a><a id="11294" class="Symbol">)</a> <a id="11296" class="Symbol">→</a> <a id="11298" href="plfa.part1.Connectives.html#10464" class="Function">case-⊎</a> <a id="11305" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="11310" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="11315" href="plfa.part1.Connectives.html#11285" class="Bound">w</a> <a id="11317" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11319" href="plfa.part1.Connectives.html#11285" class="Bound">w</a>
<a id="11321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11264" class="Function">η-⊎</a> <a id="11325" class="Symbol">(</a><a id="11326" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="11331" href="plfa.part1.Connectives.html#11331" class="Bound">x</a><a id="11332" class="Symbol">)</a> <a id="11334" class="Symbol">=</a> <a id="11336" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="11341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11264" class="Function">η-⊎</a> <a id="11345" class="Symbol">(</a><a id="11346" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="11351" href="plfa.part1.Connectives.html#11351" class="Bound">y</a><a id="11352" class="Symbol">)</a> <a id="11354" class="Symbol">=</a> <a id="11356" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}More generally, we can also throw in an arbitrary function from a disjunction:
{% raw %}<pre class="Agda"><a id="uniq-⊎"></a><a id="11448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11448" class="Function">uniq-⊎</a> <a id="11455" class="Symbol">:</a> <a id="11457" class="Symbol">∀</a> <a id="11459" class="Symbol">{</a><a id="11460" href="plfa.part1.Connectives.html#11460" class="Bound">A</a> <a id="11462" href="plfa.part1.Connectives.html#11462" class="Bound">B</a> <a id="11464" href="plfa.part1.Connectives.html#11464" class="Bound">C</a> <a id="11466" class="Symbol">:</a> <a id="11468" class="PrimitiveType">Set</a><a id="11471" class="Symbol">}</a> <a id="11473" class="Symbol">(</a><a id="11474" href="plfa.part1.Connectives.html#11474" class="Bound">h</a> <a id="11476" class="Symbol">:</a> <a id="11478" href="plfa.part1.Connectives.html#11460" class="Bound">A</a> <a id="11480" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="11482" href="plfa.part1.Connectives.html#11462" class="Bound">B</a> <a id="11484" class="Symbol">→</a> <a id="11486" href="plfa.part1.Connectives.html#11464" class="Bound">C</a><a id="11487" class="Symbol">)</a> <a id="11489" class="Symbol">(</a><a id="11490" href="plfa.part1.Connectives.html#11490" class="Bound">w</a> <a id="11492" class="Symbol">:</a> <a id="11494" href="plfa.part1.Connectives.html#11460" class="Bound">A</a> <a id="11496" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="11498" href="plfa.part1.Connectives.html#11462" class="Bound">B</a><a id="11499" class="Symbol">)</a> <a id="11501" class="Symbol">→</a>
  <a id="11505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10464" class="Function">case-⊎</a> <a id="11512" class="Symbol">(</a><a id="11513" href="plfa.part1.Connectives.html#11474" class="Bound">h</a> <a id="11515" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="11517" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a><a id="11521" class="Symbol">)</a> <a id="11523" class="Symbol">(</a><a id="11524" href="plfa.part1.Connectives.html#11474" class="Bound">h</a> <a id="11526" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="11528" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a><a id="11532" class="Symbol">)</a> <a id="11534" href="plfa.part1.Connectives.html#11490" class="Bound">w</a> <a id="11536" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11538" href="plfa.part1.Connectives.html#11474" class="Bound">h</a> <a id="11540" href="plfa.part1.Connectives.html#11490" class="Bound">w</a>
<a id="11542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11448" class="Function">uniq-⊎</a> <a id="11549" href="plfa.part1.Connectives.html#11549" class="Bound">h</a> <a id="11551" class="Symbol">(</a><a id="11552" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="11557" href="plfa.part1.Connectives.html#11557" class="Bound">x</a><a id="11558" class="Symbol">)</a> <a id="11560" class="Symbol">=</a> <a id="11562" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="11567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#11448" class="Function">uniq-⊎</a> <a id="11574" href="plfa.part1.Connectives.html#11574" class="Bound">h</a> <a id="11576" class="Symbol">(</a><a id="11577" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="11582" href="plfa.part1.Connectives.html#11582" class="Bound">y</a><a id="11583" class="Symbol">)</a> <a id="11585" class="Symbol">=</a> <a id="11587" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the propositional equality to
simplify to the same term, and similarly for `inj₂ y`.

We set the precedence of disjunction so that it binds less tightly
than any other declared operator:
{% raw %}<pre class="Agda"><a id="11892" class="Keyword">infix</a> <a id="11898" class="Number">1</a> <a id="11900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10060" class="Datatype Operator">_⊎_</a>
</pre>{% endraw %}Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

Given two types `A` and `B`, we refer to `A ⊎ B` as the
_sum_ of `A` and `B`.  In set theory, it is also sometimes
called the _disjoint union_, and in computing it corresponds
to a _variant record_ type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
{% raw %}<pre class="Agda"><a id="⊎-count"></a><a id="12682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12682" class="Function">⊎-count</a> <a id="12690" class="Symbol">:</a> <a id="12692" href="plfa.part1.Connectives.html#4483" class="Datatype">Bool</a> <a id="12697" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="12699" href="plfa.part1.Connectives.html#4536" class="Datatype">Tri</a> <a id="12703" class="Symbol">→</a> <a id="12705" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="12707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12682" class="Function">⊎-count</a> <a id="12715" class="Symbol">(</a><a id="12716" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="12721" href="plfa.part1.Connectives.html#4502" class="InductiveConstructor">true</a><a id="12725" class="Symbol">)</a>   <a id="12729" class="Symbol">=</a>  <a id="12732" class="Number">1</a>
<a id="12734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12682" class="Function">⊎-count</a> <a id="12742" class="Symbol">(</a><a id="12743" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="12748" href="plfa.part1.Connectives.html#4517" class="InductiveConstructor">false</a><a id="12753" class="Symbol">)</a>  <a id="12756" class="Symbol">=</a>  <a id="12759" class="Number">2</a>
<a id="12761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12682" class="Function">⊎-count</a> <a id="12769" class="Symbol">(</a><a id="12770" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="12775" href="plfa.part1.Connectives.html#4554" class="InductiveConstructor">aa</a><a id="12777" class="Symbol">)</a>     <a id="12783" class="Symbol">=</a>  <a id="12786" class="Number">3</a>
<a id="12788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12682" class="Function">⊎-count</a> <a id="12796" class="Symbol">(</a><a id="12797" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="12802" href="plfa.part1.Connectives.html#4565" class="InductiveConstructor">bb</a><a id="12804" class="Symbol">)</a>     <a id="12810" class="Symbol">=</a>  <a id="12813" class="Number">4</a>
<a id="12815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#12682" class="Function">⊎-count</a> <a id="12823" class="Symbol">(</a><a id="12824" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="12829" href="plfa.part1.Connectives.html#4576" class="InductiveConstructor">cc</a><a id="12831" class="Symbol">)</a>     <a id="12837" class="Symbol">=</a>  <a id="12840" class="Number">5</a>
</pre>{% endraw %}
Sum on types also shares a property with sum on numbers in that it is
commutative and associative _up to isomorphism_.

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

{% raw %}<pre class="Agda"><a id="13053" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-assoc` (practice)

Show sum is associative up to isomorphism.

{% raw %}<pre class="Agda"><a id="13165" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## False is empty

False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type:
{% raw %}<pre class="Agda"><a id="13303" class="Keyword">data</a> <a id="⊥"></a><a id="13308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#13308" class="Datatype">⊥</a> <a id="13310" class="Symbol">:</a> <a id="13312" class="PrimitiveType">Set</a> <a id="13316" class="Keyword">where</a>
  <a id="13324" class="Comment">-- no clauses!</a>
</pre>{% endraw %}There is no possible evidence that `⊥` holds.

Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the Latin phrase _ex falso_, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows:
{% raw %}<pre class="Agda"><a id="⊥-elim"></a><a id="13842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#13842" class="Function">⊥-elim</a> <a id="13849" class="Symbol">:</a> <a id="13851" class="Symbol">∀</a> <a id="13853" class="Symbol">{</a><a id="13854" href="plfa.part1.Connectives.html#13854" class="Bound">A</a> <a id="13856" class="Symbol">:</a> <a id="13858" class="PrimitiveType">Set</a><a id="13861" class="Symbol">}</a>
  <a id="13865" class="Symbol">→</a> <a id="13867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#13308" class="Datatype">⊥</a>
    <a id="13873" class="Comment">--</a>
  <a id="13878" class="Symbol">→</a> <a id="13880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#13854" class="Bound">A</a>
<a id="13882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#13842" class="Function">⊥-elim</a> <a id="13889" class="Symbol">()</a>
</pre>{% endraw %}This is our first use of the _absurd pattern_ `()`.
Here since `⊥` is a type with no members, we indicate that it is
_never_ possible to match against a value of this type by using
the pattern `()`.

The nullary case of `case-⊎` is `⊥-elim`.  By analogy,
we might have called it `case-⊥`, but chose to stick with the name
in the standard library.

The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`:
{% raw %}<pre class="Agda"><a id="uniq-⊥"></a><a id="14363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14363" class="Function">uniq-⊥</a> <a id="14370" class="Symbol">:</a> <a id="14372" class="Symbol">∀</a> <a id="14374" class="Symbol">{</a><a id="14375" href="plfa.part1.Connectives.html#14375" class="Bound">C</a> <a id="14377" class="Symbol">:</a> <a id="14379" class="PrimitiveType">Set</a><a id="14382" class="Symbol">}</a> <a id="14384" class="Symbol">(</a><a id="14385" href="plfa.part1.Connectives.html#14385" class="Bound">h</a> <a id="14387" class="Symbol">:</a> <a id="14389" href="plfa.part1.Connectives.html#13308" class="Datatype">⊥</a> <a id="14391" class="Symbol">→</a> <a id="14393" href="plfa.part1.Connectives.html#14375" class="Bound">C</a><a id="14394" class="Symbol">)</a> <a id="14396" class="Symbol">(</a><a id="14397" href="plfa.part1.Connectives.html#14397" class="Bound">w</a> <a id="14399" class="Symbol">:</a> <a id="14401" href="plfa.part1.Connectives.html#13308" class="Datatype">⊥</a><a id="14402" class="Symbol">)</a> <a id="14404" class="Symbol">→</a> <a id="14406" href="plfa.part1.Connectives.html#13842" class="Function">⊥-elim</a> <a id="14413" href="plfa.part1.Connectives.html#14397" class="Bound">w</a> <a id="14415" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14417" href="plfa.part1.Connectives.html#14385" class="Bound">h</a> <a id="14419" href="plfa.part1.Connectives.html#14397" class="Bound">w</a>
<a id="14421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14363" class="Function">uniq-⊥</a> <a id="14428" href="plfa.part1.Connectives.html#14428" class="Bound">h</a> <a id="14430" class="Symbol">()</a>
</pre>{% endraw %}Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.

We refer to `⊥` as the _empty_ type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
{% raw %}<pre class="Agda"><a id="⊥-count"></a><a id="14704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14704" class="Function">⊥-count</a> <a id="14712" class="Symbol">:</a> <a id="14714" href="plfa.part1.Connectives.html#13308" class="Datatype">⊥</a> <a id="14716" class="Symbol">→</a> <a id="14718" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="14720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#14704" class="Function">⊥-count</a> <a id="14728" class="Symbol">()</a>
</pre>{% endraw %}Here again the absurd pattern `()` indicates that no value can match
type `⊥`.

For numbers, zero is the identity of addition. Correspondingly, empty
is the identity of sums _up to isomorphism_.

#### Exercise `⊥-identityˡ` (recommended)

Show empty is the left identity of sums up to isomorphism.

{% raw %}<pre class="Agda"><a id="15038" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊥-identityʳ` (practice)

Show empty is the right identity of sums up to isomorphism.

{% raw %}<pre class="Agda"><a id="15171" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Implication is function {#implication}

Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.

Evidence that `A → B` holds is of the form

    λ (x : A) → N

where `N` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.

Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds:
{% raw %}<pre class="Agda"><a id="→-elim"></a><a id="15974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15974" class="Function">→-elim</a> <a id="15981" class="Symbol">:</a> <a id="15983" class="Symbol">∀</a> <a id="15985" class="Symbol">{</a><a id="15986" href="plfa.part1.Connectives.html#15986" class="Bound">A</a> <a id="15988" href="plfa.part1.Connectives.html#15988" class="Bound">B</a> <a id="15990" class="Symbol">:</a> <a id="15992" class="PrimitiveType">Set</a><a id="15995" class="Symbol">}</a>
  <a id="15999" class="Symbol">→</a> <a id="16001" class="Symbol">(</a><a id="16002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15986" class="Bound">A</a> <a id="16004" class="Symbol">→</a> <a id="16006" href="plfa.part1.Connectives.html#15988" class="Bound">B</a><a id="16007" class="Symbol">)</a>
  <a id="16011" class="Symbol">→</a> <a id="16013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15986" class="Bound">A</a>
    <a id="16019" class="Comment">-------</a>
  <a id="16029" class="Symbol">→</a> <a id="16031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15988" class="Bound">B</a>
<a id="16033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#15974" class="Function">→-elim</a> <a id="16040" href="plfa.part1.Connectives.html#16040" class="Bound">L</a> <a id="16042" href="plfa.part1.Connectives.html#16042" class="Bound">M</a> <a id="16044" class="Symbol">=</a> <a id="16046" href="plfa.part1.Connectives.html#16040" class="Bound">L</a> <a id="16048" href="plfa.part1.Connectives.html#16042" class="Bound">M</a>
</pre>{% endraw %}In medieval times, this rule was known by the name _modus ponens_.
It corresponds to function application.

Defining a function, with a named definition or a lambda abstraction,
is referred to as _introducing_ a function,
while applying a function is referred to as _eliminating_ the function.

Elimination followed by introduction is the identity:
{% raw %}<pre class="Agda"><a id="η-→"></a><a id="16407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#16407" class="Function">η-→</a> <a id="16411" class="Symbol">:</a> <a id="16413" class="Symbol">∀</a> <a id="16415" class="Symbol">{</a><a id="16416" href="plfa.part1.Connectives.html#16416" class="Bound">A</a> <a id="16418" href="plfa.part1.Connectives.html#16418" class="Bound">B</a> <a id="16420" class="Symbol">:</a> <a id="16422" class="PrimitiveType">Set</a><a id="16425" class="Symbol">}</a> <a id="16427" class="Symbol">(</a><a id="16428" href="plfa.part1.Connectives.html#16428" class="Bound">f</a> <a id="16430" class="Symbol">:</a> <a id="16432" href="plfa.part1.Connectives.html#16416" class="Bound">A</a> <a id="16434" class="Symbol">→</a> <a id="16436" href="plfa.part1.Connectives.html#16418" class="Bound">B</a><a id="16437" class="Symbol">)</a> <a id="16439" class="Symbol">→</a> <a id="16441" class="Symbol">(λ</a> <a id="16444" class="Symbol">(</a><a id="16445" href="plfa.part1.Connectives.html#16445" class="Bound">x</a> <a id="16447" class="Symbol">:</a> <a id="16449" href="plfa.part1.Connectives.html#16416" class="Bound">A</a><a id="16450" class="Symbol">)</a> <a id="16452" class="Symbol">→</a> <a id="16454" href="plfa.part1.Connectives.html#16428" class="Bound">f</a> <a id="16456" href="plfa.part1.Connectives.html#16445" class="Bound">x</a><a id="16457" class="Symbol">)</a> <a id="16459" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16461" href="plfa.part1.Connectives.html#16428" class="Bound">f</a>
<a id="16463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#16407" class="Function">η-→</a> <a id="16467" href="plfa.part1.Connectives.html#16467" class="Bound">f</a> <a id="16469" class="Symbol">=</a> <a id="16471" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.

Given two types `A` and `B`, we refer to `A → B` as the _function_
space from `A` to `B`.  It is also sometimes called the _exponential_,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `nᵐ` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. Then the type `Bool → Tri` has nine (that is,
three squared) members:

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
{% raw %}<pre class="Agda"><a id="→-count"></a><a id="17479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#17479" class="Function">→-count</a> <a id="17487" class="Symbol">:</a> <a id="17489" class="Symbol">(</a><a id="17490" href="plfa.part1.Connectives.html#4483" class="Datatype">Bool</a> <a id="17495" class="Symbol">→</a> <a id="17497" href="plfa.part1.Connectives.html#4536" class="Datatype">Tri</a><a id="17500" class="Symbol">)</a> <a id="17502" class="Symbol">→</a> <a id="17504" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="17506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#17479" class="Function">→-count</a> <a id="17514" href="plfa.part1.Connectives.html#17514" class="Bound">f</a> <a id="17516" class="Keyword">with</a> <a id="17521" href="plfa.part1.Connectives.html#17514" class="Bound">f</a> <a id="17523" href="plfa.part1.Connectives.html#4502" class="InductiveConstructor">true</a> <a id="17528" class="Symbol">|</a> <a id="17530" href="plfa.part1.Connectives.html#17514" class="Bound">f</a> <a id="17532" href="plfa.part1.Connectives.html#4517" class="InductiveConstructor">false</a>
<a id="17538" class="Symbol">...</a>          <a id="17551" class="Symbol">|</a> <a id="17553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4554" class="InductiveConstructor">aa</a>     <a id="17560" class="Symbol">|</a> <a id="17562" href="plfa.part1.Connectives.html#4554" class="InductiveConstructor">aa</a>      <a id="17570" class="Symbol">=</a>   <a id="17574" class="Number">1</a>
<a id="17576" class="Symbol">...</a>          <a id="17589" class="Symbol">|</a> <a id="17591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4554" class="InductiveConstructor">aa</a>     <a id="17598" class="Symbol">|</a> <a id="17600" href="plfa.part1.Connectives.html#4565" class="InductiveConstructor">bb</a>      <a id="17608" class="Symbol">=</a>   <a id="17612" class="Number">2</a>
<a id="17614" class="Symbol">...</a>          <a id="17627" class="Symbol">|</a> <a id="17629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4554" class="InductiveConstructor">aa</a>     <a id="17636" class="Symbol">|</a> <a id="17638" href="plfa.part1.Connectives.html#4576" class="InductiveConstructor">cc</a>      <a id="17646" class="Symbol">=</a>   <a id="17650" class="Number">3</a>
<a id="17652" class="Symbol">...</a>          <a id="17665" class="Symbol">|</a> <a id="17667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4565" class="InductiveConstructor">bb</a>     <a id="17674" class="Symbol">|</a> <a id="17676" href="plfa.part1.Connectives.html#4554" class="InductiveConstructor">aa</a>      <a id="17684" class="Symbol">=</a>   <a id="17688" class="Number">4</a>
<a id="17690" class="Symbol">...</a>          <a id="17703" class="Symbol">|</a> <a id="17705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4565" class="InductiveConstructor">bb</a>     <a id="17712" class="Symbol">|</a> <a id="17714" href="plfa.part1.Connectives.html#4565" class="InductiveConstructor">bb</a>      <a id="17722" class="Symbol">=</a>   <a id="17726" class="Number">5</a>
<a id="17728" class="Symbol">...</a>          <a id="17741" class="Symbol">|</a> <a id="17743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4565" class="InductiveConstructor">bb</a>     <a id="17750" class="Symbol">|</a> <a id="17752" href="plfa.part1.Connectives.html#4576" class="InductiveConstructor">cc</a>      <a id="17760" class="Symbol">=</a>   <a id="17764" class="Number">6</a>
<a id="17766" class="Symbol">...</a>          <a id="17779" class="Symbol">|</a> <a id="17781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4576" class="InductiveConstructor">cc</a>     <a id="17788" class="Symbol">|</a> <a id="17790" href="plfa.part1.Connectives.html#4554" class="InductiveConstructor">aa</a>      <a id="17798" class="Symbol">=</a>   <a id="17802" class="Number">7</a>
<a id="17804" class="Symbol">...</a>          <a id="17817" class="Symbol">|</a> <a id="17819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4576" class="InductiveConstructor">cc</a>     <a id="17826" class="Symbol">|</a> <a id="17828" href="plfa.part1.Connectives.html#4565" class="InductiveConstructor">bb</a>      <a id="17836" class="Symbol">=</a>   <a id="17840" class="Number">8</a>
<a id="17842" class="Symbol">...</a>          <a id="17855" class="Symbol">|</a> <a id="17857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#4576" class="InductiveConstructor">cc</a>     <a id="17864" class="Symbol">|</a> <a id="17866" href="plfa.part1.Connectives.html#4576" class="InductiveConstructor">cc</a>      <a id="17874" class="Symbol">=</a>   <a id="17878" class="Number">9</a>
</pre>{% endraw %}
Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.

Corresponding to the law

    (p ^ n) ^ m  ≡  p ^ (n * m)

we have the isomorphism

    A → (B → C)  ≃  (A × B) → C

Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality:
{% raw %}<pre class="Agda"><a id="currying"></a><a id="18404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#18404" class="Function">currying</a> <a id="18413" class="Symbol">:</a> <a id="18415" class="Symbol">∀</a> <a id="18417" class="Symbol">{</a><a id="18418" href="plfa.part1.Connectives.html#18418" class="Bound">A</a> <a id="18420" href="plfa.part1.Connectives.html#18420" class="Bound">B</a> <a id="18422" href="plfa.part1.Connectives.html#18422" class="Bound">C</a> <a id="18424" class="Symbol">:</a> <a id="18426" class="PrimitiveType">Set</a><a id="18429" class="Symbol">}</a> <a id="18431" class="Symbol">→</a> <a id="18433" class="Symbol">(</a><a id="18434" href="plfa.part1.Connectives.html#18418" class="Bound">A</a> <a id="18436" class="Symbol">→</a> <a id="18438" href="plfa.part1.Connectives.html#18420" class="Bound">B</a> <a id="18440" class="Symbol">→</a> <a id="18442" href="plfa.part1.Connectives.html#18422" class="Bound">C</a><a id="18443" class="Symbol">)</a> <a id="18445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="18447" class="Symbol">(</a><a id="18448" href="plfa.part1.Connectives.html#18418" class="Bound">A</a> <a id="18450" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="18452" href="plfa.part1.Connectives.html#18420" class="Bound">B</a> <a id="18454" class="Symbol">→</a> <a id="18456" href="plfa.part1.Connectives.html#18422" class="Bound">C</a><a id="18457" class="Symbol">)</a>
<a id="18459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#18404" class="Function">currying</a> <a id="18468" class="Symbol">=</a>
  <a id="18472" class="Keyword">record</a>
    <a id="18483" class="Symbol">{</a> <a id="18485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="18493" class="Symbol">=</a>  <a id="18496" class="Symbol">λ{</a> <a id="18499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#18499" class="Bound">f</a> <a id="18501" class="Symbol">→</a> <a id="18503" class="Symbol">λ{</a> <a id="18506" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="18508" href="plfa.part1.Connectives.html#18508" class="Bound">x</a> <a id="18510" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="18512" href="plfa.part1.Connectives.html#18512" class="Bound">y</a> <a id="18514" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="18516" class="Symbol">→</a> <a id="18518" href="plfa.part1.Connectives.html#18499" class="Bound">f</a> <a id="18520" href="plfa.part1.Connectives.html#18508" class="Bound">x</a> <a id="18522" href="plfa.part1.Connectives.html#18512" class="Bound">y</a> <a id="18524" class="Symbol">}}</a>
    <a id="18531" class="Symbol">;</a> <a id="18533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="18541" class="Symbol">=</a>  <a id="18544" class="Symbol">λ{</a> <a id="18547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#18547" class="Bound">g</a> <a id="18549" class="Symbol">→</a> <a id="18551" class="Symbol">λ{</a> <a id="18554" href="plfa.part1.Connectives.html#18554" class="Bound">x</a> <a id="18556" class="Symbol">→</a> <a id="18558" class="Symbol">λ{</a> <a id="18561" href="plfa.part1.Connectives.html#18561" class="Bound">y</a> <a id="18563" class="Symbol">→</a> <a id="18565" href="plfa.part1.Connectives.html#18547" class="Bound">g</a> <a id="18567" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="18569" href="plfa.part1.Connectives.html#18554" class="Bound">x</a> <a id="18571" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="18573" href="plfa.part1.Connectives.html#18561" class="Bound">y</a> <a id="18575" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="18577" class="Symbol">}}}</a>
    <a id="18585" class="Symbol">;</a> <a id="18587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="18595" class="Symbol">=</a>  <a id="18598" class="Symbol">λ{</a> <a id="18601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#18601" class="Bound">f</a> <a id="18603" class="Symbol">→</a> <a id="18605" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="18610" class="Symbol">}</a>
    <a id="18616" class="Symbol">;</a> <a id="18618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="18626" class="Symbol">=</a>  <a id="18629" class="Symbol">λ{</a> <a id="18632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#18632" class="Bound">g</a> <a id="18634" class="Symbol">→</a> <a id="18636" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="18651" class="Symbol">λ{</a> <a id="18654" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="18656" href="plfa.part1.Connectives.html#18656" class="Bound">x</a> <a id="18658" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="18660" href="plfa.part1.Connectives.html#18660" class="Bound">y</a> <a id="18662" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="18664" class="Symbol">→</a> <a id="18666" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="18671" class="Symbol">}}</a>
    <a id="18678" class="Symbol">}</a>
</pre>{% endraw %}
Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, our way of writing addition

    _+_ : ℕ → ℕ → ℕ

is isomorphic to a function that accepts a pair of arguments:

    _+′_ : (ℕ × ℕ) → ℕ

Agda is optimised for currying, so `2 + 3` abbreviates `_+_ 2 3`.
In a language optimised for pairing, we would instead take `2 +′ 3` as
an abbreviation for `_+′_ ⟨ 2 , 3 ⟩`.

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have the isomorphism:

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.  The proof of the left inverse requires extensionality:
{% raw %}<pre class="Agda"><a id="→-distrib-⊎"></a><a id="19565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#19565" class="Function">→-distrib-⊎</a> <a id="19577" class="Symbol">:</a> <a id="19579" class="Symbol">∀</a> <a id="19581" class="Symbol">{</a><a id="19582" href="plfa.part1.Connectives.html#19582" class="Bound">A</a> <a id="19584" href="plfa.part1.Connectives.html#19584" class="Bound">B</a> <a id="19586" href="plfa.part1.Connectives.html#19586" class="Bound">C</a> <a id="19588" class="Symbol">:</a> <a id="19590" class="PrimitiveType">Set</a><a id="19593" class="Symbol">}</a> <a id="19595" class="Symbol">→</a> <a id="19597" class="Symbol">(</a><a id="19598" href="plfa.part1.Connectives.html#19582" class="Bound">A</a> <a id="19600" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="19602" href="plfa.part1.Connectives.html#19584" class="Bound">B</a> <a id="19604" class="Symbol">→</a> <a id="19606" href="plfa.part1.Connectives.html#19586" class="Bound">C</a><a id="19607" class="Symbol">)</a> <a id="19609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="19611" class="Symbol">((</a><a id="19613" href="plfa.part1.Connectives.html#19582" class="Bound">A</a> <a id="19615" class="Symbol">→</a> <a id="19617" href="plfa.part1.Connectives.html#19586" class="Bound">C</a><a id="19618" class="Symbol">)</a> <a id="19620" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="19622" class="Symbol">(</a><a id="19623" href="plfa.part1.Connectives.html#19584" class="Bound">B</a> <a id="19625" class="Symbol">→</a> <a id="19627" href="plfa.part1.Connectives.html#19586" class="Bound">C</a><a id="19628" class="Symbol">))</a>
<a id="19631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#19565" class="Function">→-distrib-⊎</a> <a id="19643" class="Symbol">=</a>
  <a id="19647" class="Keyword">record</a>
    <a id="19658" class="Symbol">{</a> <a id="19660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="19668" class="Symbol">=</a> <a id="19670" class="Symbol">λ{</a> <a id="19673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#19673" class="Bound">f</a> <a id="19675" class="Symbol">→</a> <a id="19677" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="19679" href="plfa.part1.Connectives.html#19673" class="Bound">f</a> <a id="19681" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="19683" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="19688" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="19690" href="plfa.part1.Connectives.html#19673" class="Bound">f</a> <a id="19692" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="19694" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="19699" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="19701" class="Symbol">}</a>
    <a id="19707" class="Symbol">;</a> <a id="19709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="19717" class="Symbol">=</a> <a id="19719" class="Symbol">λ{</a> <a id="19722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="19724" href="plfa.part1.Connectives.html#19724" class="Bound">g</a> <a id="19726" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="19728" href="plfa.part1.Connectives.html#19728" class="Bound">h</a> <a id="19730" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="19732" class="Symbol">→</a> <a id="19734" class="Symbol">λ{</a> <a id="19737" class="Symbol">(</a><a id="19738" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="19743" href="plfa.part1.Connectives.html#19743" class="Bound">x</a><a id="19744" class="Symbol">)</a> <a id="19746" class="Symbol">→</a> <a id="19748" href="plfa.part1.Connectives.html#19724" class="Bound">g</a> <a id="19750" href="plfa.part1.Connectives.html#19743" class="Bound">x</a> <a id="19752" class="Symbol">;</a> <a id="19754" class="Symbol">(</a><a id="19755" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="19760" href="plfa.part1.Connectives.html#19760" class="Bound">y</a><a id="19761" class="Symbol">)</a> <a id="19763" class="Symbol">→</a> <a id="19765" href="plfa.part1.Connectives.html#19728" class="Bound">h</a> <a id="19767" href="plfa.part1.Connectives.html#19760" class="Bound">y</a> <a id="19769" class="Symbol">}</a> <a id="19771" class="Symbol">}</a>
    <a id="19777" class="Symbol">;</a> <a id="19779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="19787" class="Symbol">=</a> <a id="19789" class="Symbol">λ{</a> <a id="19792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#19792" class="Bound">f</a> <a id="19794" class="Symbol">→</a> <a id="19796" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="19811" class="Symbol">λ{</a> <a id="19814" class="Symbol">(</a><a id="19815" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="19820" href="plfa.part1.Connectives.html#19820" class="Bound">x</a><a id="19821" class="Symbol">)</a> <a id="19823" class="Symbol">→</a> <a id="19825" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19830" class="Symbol">;</a> <a id="19832" class="Symbol">(</a><a id="19833" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="19838" href="plfa.part1.Connectives.html#19838" class="Bound">y</a><a id="19839" class="Symbol">)</a> <a id="19841" class="Symbol">→</a> <a id="19843" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19848" class="Symbol">}</a> <a id="19850" class="Symbol">}</a>
    <a id="19856" class="Symbol">;</a> <a id="19858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="19866" class="Symbol">=</a> <a id="19868" class="Symbol">λ{</a> <a id="19871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="19873" href="plfa.part1.Connectives.html#19873" class="Bound">g</a> <a id="19875" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="19877" href="plfa.part1.Connectives.html#19877" class="Bound">h</a> <a id="19879" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="19881" class="Symbol">→</a> <a id="19883" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19888" class="Symbol">}</a>
    <a id="19894" class="Symbol">}</a>
</pre>{% endraw %}
Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have the isomorphism:

    A → B × C  ≃  (A → B) × (A → C)

That is, the assertion that if `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof of left inverse requires both extensionality
and the rule `η-×` for products:
{% raw %}<pre class="Agda"><a id="→-distrib-×"></a><a id="20285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20285" class="Function">→-distrib-×</a> <a id="20297" class="Symbol">:</a> <a id="20299" class="Symbol">∀</a> <a id="20301" class="Symbol">{</a><a id="20302" href="plfa.part1.Connectives.html#20302" class="Bound">A</a> <a id="20304" href="plfa.part1.Connectives.html#20304" class="Bound">B</a> <a id="20306" href="plfa.part1.Connectives.html#20306" class="Bound">C</a> <a id="20308" class="Symbol">:</a> <a id="20310" class="PrimitiveType">Set</a><a id="20313" class="Symbol">}</a> <a id="20315" class="Symbol">→</a> <a id="20317" class="Symbol">(</a><a id="20318" href="plfa.part1.Connectives.html#20302" class="Bound">A</a> <a id="20320" class="Symbol">→</a> <a id="20322" href="plfa.part1.Connectives.html#20304" class="Bound">B</a> <a id="20324" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="20326" href="plfa.part1.Connectives.html#20306" class="Bound">C</a><a id="20327" class="Symbol">)</a> <a id="20329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="20331" class="Symbol">(</a><a id="20332" href="plfa.part1.Connectives.html#20302" class="Bound">A</a> <a id="20334" class="Symbol">→</a> <a id="20336" href="plfa.part1.Connectives.html#20304" class="Bound">B</a><a id="20337" class="Symbol">)</a> <a id="20339" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="20341" class="Symbol">(</a><a id="20342" href="plfa.part1.Connectives.html#20302" class="Bound">A</a> <a id="20344" class="Symbol">→</a> <a id="20346" href="plfa.part1.Connectives.html#20306" class="Bound">C</a><a id="20347" class="Symbol">)</a>
<a id="20349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20285" class="Function">→-distrib-×</a> <a id="20361" class="Symbol">=</a>
  <a id="20365" class="Keyword">record</a>
    <a id="20376" class="Symbol">{</a> <a id="20378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="20386" class="Symbol">=</a> <a id="20388" class="Symbol">λ{</a> <a id="20391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20391" class="Bound">f</a> <a id="20393" class="Symbol">→</a> <a id="20395" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="20397" href="plfa.part1.Connectives.html#1611" class="Function">proj₁</a> <a id="20403" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="20405" href="plfa.part1.Connectives.html#20391" class="Bound">f</a> <a id="20407" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20409" href="plfa.part1.Connectives.html#1680" class="Function">proj₂</a> <a id="20415" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="20417" href="plfa.part1.Connectives.html#20391" class="Bound">f</a> <a id="20419" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="20421" class="Symbol">}</a>
    <a id="20427" class="Symbol">;</a> <a id="20429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="20437" class="Symbol">=</a> <a id="20439" class="Symbol">λ{</a> <a id="20442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="20444" href="plfa.part1.Connectives.html#20444" class="Bound">g</a> <a id="20446" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20448" href="plfa.part1.Connectives.html#20448" class="Bound">h</a> <a id="20450" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="20452" class="Symbol">→</a> <a id="20454" class="Symbol">λ</a> <a id="20456" href="plfa.part1.Connectives.html#20456" class="Bound">x</a> <a id="20458" class="Symbol">→</a> <a id="20460" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="20462" href="plfa.part1.Connectives.html#20444" class="Bound">g</a> <a id="20464" href="plfa.part1.Connectives.html#20456" class="Bound">x</a> <a id="20466" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20468" href="plfa.part1.Connectives.html#20448" class="Bound">h</a> <a id="20470" href="plfa.part1.Connectives.html#20456" class="Bound">x</a> <a id="20472" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="20474" class="Symbol">}</a>
    <a id="20480" class="Symbol">;</a> <a id="20482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="20490" class="Symbol">=</a> <a id="20492" class="Symbol">λ{</a> <a id="20495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20495" class="Bound">f</a> <a id="20497" class="Symbol">→</a> <a id="20499" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="20514" class="Symbol">λ{</a> <a id="20517" href="plfa.part1.Connectives.html#20517" class="Bound">x</a> <a id="20519" class="Symbol">→</a> <a id="20521" href="plfa.part1.Connectives.html#3562" class="Function">η-×</a> <a id="20525" class="Symbol">(</a><a id="20526" href="plfa.part1.Connectives.html#20495" class="Bound">f</a> <a id="20528" href="plfa.part1.Connectives.html#20517" class="Bound">x</a><a id="20529" class="Symbol">)</a> <a id="20531" class="Symbol">}</a> <a id="20533" class="Symbol">}</a>
    <a id="20539" class="Symbol">;</a> <a id="20541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="20549" class="Symbol">=</a> <a id="20551" class="Symbol">λ{</a> <a id="20554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="20556" href="plfa.part1.Connectives.html#20556" class="Bound">g</a> <a id="20558" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20560" href="plfa.part1.Connectives.html#20560" class="Bound">h</a> <a id="20562" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="20564" class="Symbol">→</a> <a id="20566" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="20571" class="Symbol">}</a>
    <a id="20577" class="Symbol">}</a>
</pre>{% endraw %}

## Distribution

Products distribute over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results:
{% raw %}<pre class="Agda"><a id="×-distrib-⊎"></a><a id="20736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20736" class="Function">×-distrib-⊎</a> <a id="20748" class="Symbol">:</a> <a id="20750" class="Symbol">∀</a> <a id="20752" class="Symbol">{</a><a id="20753" href="plfa.part1.Connectives.html#20753" class="Bound">A</a> <a id="20755" href="plfa.part1.Connectives.html#20755" class="Bound">B</a> <a id="20757" href="plfa.part1.Connectives.html#20757" class="Bound">C</a> <a id="20759" class="Symbol">:</a> <a id="20761" class="PrimitiveType">Set</a><a id="20764" class="Symbol">}</a> <a id="20766" class="Symbol">→</a> <a id="20768" class="Symbol">(</a><a id="20769" href="plfa.part1.Connectives.html#20753" class="Bound">A</a> <a id="20771" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="20773" href="plfa.part1.Connectives.html#20755" class="Bound">B</a><a id="20774" class="Symbol">)</a> <a id="20776" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="20778" href="plfa.part1.Connectives.html#20757" class="Bound">C</a> <a id="20780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="20782" class="Symbol">(</a><a id="20783" href="plfa.part1.Connectives.html#20753" class="Bound">A</a> <a id="20785" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="20787" href="plfa.part1.Connectives.html#20757" class="Bound">C</a><a id="20788" class="Symbol">)</a> <a id="20790" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="20792" class="Symbol">(</a><a id="20793" href="plfa.part1.Connectives.html#20755" class="Bound">B</a> <a id="20795" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="20797" href="plfa.part1.Connectives.html#20757" class="Bound">C</a><a id="20798" class="Symbol">)</a>
<a id="20800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#20736" class="Function">×-distrib-⊎</a> <a id="20812" class="Symbol">=</a>
  <a id="20816" class="Keyword">record</a>
    <a id="20827" class="Symbol">{</a> <a id="20829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="20837" class="Symbol">=</a> <a id="20839" class="Symbol">λ{</a> <a id="20842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="20844" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="20849" href="plfa.part1.Connectives.html#20849" class="Bound">x</a> <a id="20851" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20853" href="plfa.part1.Connectives.html#20853" class="Bound">z</a> <a id="20855" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="20857" class="Symbol">→</a> <a id="20859" class="Symbol">(</a><a id="20860" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="20865" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="20867" href="plfa.part1.Connectives.html#20849" class="Bound">x</a> <a id="20869" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20871" href="plfa.part1.Connectives.html#20853" class="Bound">z</a> <a id="20873" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a><a id="20874" class="Symbol">)</a>
                 <a id="20893" class="Symbol">;</a> <a id="20895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="20897" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="20902" href="plfa.part1.Connectives.html#20902" class="Bound">y</a> <a id="20904" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20906" href="plfa.part1.Connectives.html#20906" class="Bound">z</a> <a id="20908" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="20910" class="Symbol">→</a> <a id="20912" class="Symbol">(</a><a id="20913" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="20918" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="20920" href="plfa.part1.Connectives.html#20902" class="Bound">y</a> <a id="20922" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20924" href="plfa.part1.Connectives.html#20906" class="Bound">z</a> <a id="20926" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a><a id="20927" class="Symbol">)</a>
                 <a id="20946" class="Symbol">}</a>
    <a id="20952" class="Symbol">;</a> <a id="20954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="20962" class="Symbol">=</a> <a id="20964" class="Symbol">λ{</a> <a id="20967" class="Symbol">(</a><a id="20968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10091" class="InductiveConstructor">inj₁</a> <a id="20973" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="20975" href="plfa.part1.Connectives.html#20975" class="Bound">x</a> <a id="20977" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20979" href="plfa.part1.Connectives.html#20979" class="Bound">z</a> <a id="20981" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a><a id="20982" class="Symbol">)</a> <a id="20984" class="Symbol">→</a> <a id="20986" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="20988" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="20993" href="plfa.part1.Connectives.html#20975" class="Bound">x</a> <a id="20995" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="20997" href="plfa.part1.Connectives.html#20979" class="Bound">z</a> <a id="20999" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>
                 <a id="21018" class="Symbol">;</a> <a id="21020" class="Symbol">(</a><a id="21021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10133" class="InductiveConstructor">inj₂</a> <a id="21026" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="21028" href="plfa.part1.Connectives.html#21028" class="Bound">y</a> <a id="21030" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21032" href="plfa.part1.Connectives.html#21032" class="Bound">z</a> <a id="21034" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a><a id="21035" class="Symbol">)</a> <a id="21037" class="Symbol">→</a> <a id="21039" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="21041" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="21046" href="plfa.part1.Connectives.html#21028" class="Bound">y</a> <a id="21048" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21050" href="plfa.part1.Connectives.html#21032" class="Bound">z</a> <a id="21052" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>
                 <a id="21071" class="Symbol">}</a>
    <a id="21077" class="Symbol">;</a> <a id="21079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="21087" class="Symbol">=</a> <a id="21089" class="Symbol">λ{</a> <a id="21092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="21094" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="21099" href="plfa.part1.Connectives.html#21099" class="Bound">x</a> <a id="21101" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21103" href="plfa.part1.Connectives.html#21103" class="Bound">z</a> <a id="21105" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="21107" class="Symbol">→</a> <a id="21109" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21131" class="Symbol">;</a> <a id="21133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="21135" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="21140" href="plfa.part1.Connectives.html#21140" class="Bound">y</a> <a id="21142" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21144" href="plfa.part1.Connectives.html#21144" class="Bound">z</a> <a id="21146" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="21148" class="Symbol">→</a> <a id="21150" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21172" class="Symbol">}</a>
    <a id="21178" class="Symbol">;</a> <a id="21180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="21188" class="Symbol">=</a> <a id="21190" class="Symbol">λ{</a> <a id="21193" class="Symbol">(</a><a id="21194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10091" class="InductiveConstructor">inj₁</a> <a id="21199" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="21201" href="plfa.part1.Connectives.html#21201" class="Bound">x</a> <a id="21203" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21205" href="plfa.part1.Connectives.html#21205" class="Bound">z</a> <a id="21207" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a><a id="21208" class="Symbol">)</a> <a id="21210" class="Symbol">→</a> <a id="21212" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21234" class="Symbol">;</a> <a id="21236" class="Symbol">(</a><a id="21237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10133" class="InductiveConstructor">inj₂</a> <a id="21242" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="21244" href="plfa.part1.Connectives.html#21244" class="Bound">y</a> <a id="21246" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21248" href="plfa.part1.Connectives.html#21248" class="Bound">z</a> <a id="21250" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a><a id="21251" class="Symbol">)</a> <a id="21253" class="Symbol">→</a> <a id="21255" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21277" class="Symbol">}</a>
    <a id="21283" class="Symbol">}</a>
</pre>{% endraw %}
Sums do not distribute over products up to isomorphism, but it is an embedding:
{% raw %}<pre class="Agda"><a id="⊎-distrib-×"></a><a id="21374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#21374" class="Function">⊎-distrib-×</a> <a id="21386" class="Symbol">:</a> <a id="21388" class="Symbol">∀</a> <a id="21390" class="Symbol">{</a><a id="21391" href="plfa.part1.Connectives.html#21391" class="Bound">A</a> <a id="21393" href="plfa.part1.Connectives.html#21393" class="Bound">B</a> <a id="21395" href="plfa.part1.Connectives.html#21395" class="Bound">C</a> <a id="21397" class="Symbol">:</a> <a id="21399" class="PrimitiveType">Set</a><a id="21402" class="Symbol">}</a> <a id="21404" class="Symbol">→</a> <a id="21406" class="Symbol">(</a><a id="21407" href="plfa.part1.Connectives.html#21391" class="Bound">A</a> <a id="21409" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="21411" href="plfa.part1.Connectives.html#21393" class="Bound">B</a><a id="21412" class="Symbol">)</a> <a id="21414" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="21416" href="plfa.part1.Connectives.html#21395" class="Bound">C</a> <a id="21418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9186" class="Record Operator">≲</a> <a id="21420" class="Symbol">(</a><a id="21421" href="plfa.part1.Connectives.html#21391" class="Bound">A</a> <a id="21423" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="21425" href="plfa.part1.Connectives.html#21395" class="Bound">C</a><a id="21426" class="Symbol">)</a> <a id="21428" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="21430" class="Symbol">(</a><a id="21431" href="plfa.part1.Connectives.html#21393" class="Bound">B</a> <a id="21433" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="21435" href="plfa.part1.Connectives.html#21395" class="Bound">C</a><a id="21436" class="Symbol">)</a>
<a id="21438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#21374" class="Function">⊎-distrib-×</a> <a id="21450" class="Symbol">=</a>
  <a id="21454" class="Keyword">record</a>
    <a id="21465" class="Symbol">{</a> <a id="21467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9226" class="Field">to</a>      <a id="21475" class="Symbol">=</a> <a id="21477" class="Symbol">λ{</a> <a id="21480" class="Symbol">(</a><a id="21481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10091" class="InductiveConstructor">inj₁</a> <a id="21486" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="21488" href="plfa.part1.Connectives.html#21488" class="Bound">x</a> <a id="21490" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21492" href="plfa.part1.Connectives.html#21492" class="Bound">y</a> <a id="21494" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a><a id="21495" class="Symbol">)</a> <a id="21497" class="Symbol">→</a> <a id="21499" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="21501" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="21506" href="plfa.part1.Connectives.html#21488" class="Bound">x</a> <a id="21508" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21510" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="21515" href="plfa.part1.Connectives.html#21492" class="Bound">y</a> <a id="21517" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>
                 <a id="21536" class="Symbol">;</a> <a id="21538" class="Symbol">(</a><a id="21539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10133" class="InductiveConstructor">inj₂</a> <a id="21544" href="plfa.part1.Connectives.html#21544" class="Bound">z</a><a id="21545" class="Symbol">)</a>         <a id="21555" class="Symbol">→</a> <a id="21557" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="21559" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="21564" href="plfa.part1.Connectives.html#21544" class="Bound">z</a> <a id="21566" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21568" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="21573" href="plfa.part1.Connectives.html#21544" class="Bound">z</a> <a id="21575" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a>
                 <a id="21594" class="Symbol">}</a>
    <a id="21600" class="Symbol">;</a> <a id="21602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9246" class="Field">from</a>    <a id="21610" class="Symbol">=</a> <a id="21612" class="Symbol">λ{</a> <a id="21615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="21617" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="21622" href="plfa.part1.Connectives.html#21622" class="Bound">x</a> <a id="21624" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21626" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="21631" href="plfa.part1.Connectives.html#21631" class="Bound">y</a> <a id="21633" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="21635" class="Symbol">→</a> <a id="21637" class="Symbol">(</a><a id="21638" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="21643" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="21645" href="plfa.part1.Connectives.html#21622" class="Bound">x</a> <a id="21647" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21649" href="plfa.part1.Connectives.html#21631" class="Bound">y</a> <a id="21651" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a><a id="21652" class="Symbol">)</a>
                 <a id="21671" class="Symbol">;</a> <a id="21673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="21675" href="plfa.part1.Connectives.html#10091" class="InductiveConstructor">inj₁</a> <a id="21680" href="plfa.part1.Connectives.html#21680" class="Bound">x</a> <a id="21682" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21684" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="21689" href="plfa.part1.Connectives.html#21689" class="Bound">z</a> <a id="21691" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="21693" class="Symbol">→</a> <a id="21695" class="Symbol">(</a><a id="21696" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="21701" href="plfa.part1.Connectives.html#21689" class="Bound">z</a><a id="21702" class="Symbol">)</a>
                 <a id="21721" class="Symbol">;</a> <a id="21723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#1326" class="InductiveConstructor Operator">⟨</a> <a id="21725" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="21730" href="plfa.part1.Connectives.html#21730" class="Bound">z</a> <a id="21732" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21734" class="Symbol">_</a>      <a id="21741" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a> <a id="21743" class="Symbol">→</a> <a id="21745" class="Symbol">(</a><a id="21746" href="plfa.part1.Connectives.html#10133" class="InductiveConstructor">inj₂</a> <a id="21751" href="plfa.part1.Connectives.html#21730" class="Bound">z</a><a id="21752" class="Symbol">)</a>
                 <a id="21771" class="Symbol">}</a>
    <a id="21777" class="Symbol">;</a> <a id="21779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9266" class="Field">from∘to</a> <a id="21787" class="Symbol">=</a> <a id="21789" class="Symbol">λ{</a> <a id="21792" class="Symbol">(</a><a id="21793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10091" class="InductiveConstructor">inj₁</a> <a id="21798" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟨</a> <a id="21800" href="plfa.part1.Connectives.html#21800" class="Bound">x</a> <a id="21802" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">,</a> <a id="21804" href="plfa.part1.Connectives.html#21804" class="Bound">y</a> <a id="21806" href="plfa.part1.Connectives.html#1326" class="InductiveConstructor Operator">⟩</a><a id="21807" class="Symbol">)</a> <a id="21809" class="Symbol">→</a> <a id="21811" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21833" class="Symbol">;</a> <a id="21835" class="Symbol">(</a><a id="21836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#10133" class="InductiveConstructor">inj₂</a> <a id="21841" href="plfa.part1.Connectives.html#21841" class="Bound">z</a><a id="21842" class="Symbol">)</a>         <a id="21852" class="Symbol">→</a> <a id="21854" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21876" class="Symbol">}</a>
    <a id="21882" class="Symbol">}</a>
</pre>{% endraw %}Note that there is a choice in how we write the `from` function.
As given, it takes `⟨ inj₂ z , inj₂ z′ ⟩` to `inj₂ z`, but it is
easy to write a variant that instead returns `inj₂ z′`.  We have
an embedding rather than an isomorphism because the
`from` function must discard either `z` or `z′` in this case.

In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:

    A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
    A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)

But when we consider the functions that provide evidence for these
implications, then the first corresponds to an isomorphism while the
second only corresponds to an embedding, revealing a sense in which
one of these laws is "more true" than the other.


#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:
{% raw %}<pre class="Agda"><a id="22735" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="22747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#22747" class="Postulate">⊎-weak-×</a> <a id="22756" class="Symbol">:</a> <a id="22758" class="Symbol">∀</a> <a id="22760" class="Symbol">{</a><a id="22761" href="plfa.part1.Connectives.html#22761" class="Bound">A</a> <a id="22763" href="plfa.part1.Connectives.html#22763" class="Bound">B</a> <a id="22765" href="plfa.part1.Connectives.html#22765" class="Bound">C</a> <a id="22767" class="Symbol">:</a> <a id="22769" class="PrimitiveType">Set</a><a id="22772" class="Symbol">}</a> <a id="22774" class="Symbol">→</a> <a id="22776" class="Symbol">(</a><a id="22777" href="plfa.part1.Connectives.html#22761" class="Bound">A</a> <a id="22779" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="22781" href="plfa.part1.Connectives.html#22763" class="Bound">B</a><a id="22782" class="Symbol">)</a> <a id="22784" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="22786" href="plfa.part1.Connectives.html#22765" class="Bound">C</a> <a id="22788" class="Symbol">→</a> <a id="22790" href="plfa.part1.Connectives.html#22761" class="Bound">A</a> <a id="22792" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="22794" class="Symbol">(</a><a id="22795" href="plfa.part1.Connectives.html#22763" class="Bound">B</a> <a id="22797" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="22799" href="plfa.part1.Connectives.html#22765" class="Bound">C</a><a id="22800" class="Symbol">)</a>
</pre>{% endraw %}This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

{% raw %}<pre class="Agda"><a id="22942" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `⊎×-implies-×⊎` (practice)

Show that a disjunct of conjuncts implies a conjunct of disjuncts:
{% raw %}<pre class="Agda"><a id="23084" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="23096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Connectives.md %}{% raw %}#23096" class="Postulate">⊎×-implies-×⊎</a> <a id="23110" class="Symbol">:</a> <a id="23112" class="Symbol">∀</a> <a id="23114" class="Symbol">{</a><a id="23115" href="plfa.part1.Connectives.html#23115" class="Bound">A</a> <a id="23117" href="plfa.part1.Connectives.html#23117" class="Bound">B</a> <a id="23119" href="plfa.part1.Connectives.html#23119" class="Bound">C</a> <a id="23121" href="plfa.part1.Connectives.html#23121" class="Bound">D</a> <a id="23123" class="Symbol">:</a> <a id="23125" class="PrimitiveType">Set</a><a id="23128" class="Symbol">}</a> <a id="23130" class="Symbol">→</a> <a id="23132" class="Symbol">(</a><a id="23133" href="plfa.part1.Connectives.html#23115" class="Bound">A</a> <a id="23135" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="23137" href="plfa.part1.Connectives.html#23117" class="Bound">B</a><a id="23138" class="Symbol">)</a> <a id="23140" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="23142" class="Symbol">(</a><a id="23143" href="plfa.part1.Connectives.html#23119" class="Bound">C</a> <a id="23145" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="23147" href="plfa.part1.Connectives.html#23121" class="Bound">D</a><a id="23148" class="Symbol">)</a> <a id="23150" class="Symbol">→</a> <a id="23152" class="Symbol">(</a><a id="23153" href="plfa.part1.Connectives.html#23115" class="Bound">A</a> <a id="23155" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="23157" href="plfa.part1.Connectives.html#23119" class="Bound">C</a><a id="23158" class="Symbol">)</a> <a id="23160" href="plfa.part1.Connectives.html#1295" class="Datatype Operator">×</a> <a id="23162" class="Symbol">(</a><a id="23163" href="plfa.part1.Connectives.html#23117" class="Bound">B</a> <a id="23165" href="plfa.part1.Connectives.html#10060" class="Datatype Operator">⊎</a> <a id="23167" href="plfa.part1.Connectives.html#23121" class="Bound">D</a><a id="23168" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, give a counterexample.

{% raw %}<pre class="Agda"><a id="23248" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="23385" class="Keyword">import</a> <a id="23392" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="23405" class="Keyword">using</a> <a id="23411" class="Symbol">(</a><a id="23412" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="23415" class="Symbol">;</a> <a id="23417" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="23422" class="Symbol">;</a> <a id="23424" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="23429" class="Symbol">)</a> <a id="23431" class="Keyword">renaming</a> <a id="23440" class="Symbol">(</a><a id="23441" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="23445" class="Symbol">to</a> <a id="23448" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="23453" class="Symbol">)</a>
<a id="23455" class="Keyword">import</a> <a id="23462" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="23472" class="Keyword">using</a> <a id="23478" class="Symbol">(</a><a id="23479" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="23480" class="Symbol">;</a> <a id="23482" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="23484" class="Symbol">)</a>
<a id="23486" class="Keyword">import</a> <a id="23493" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="23502" class="Keyword">using</a> <a id="23508" class="Symbol">(</a><a id="23509" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="23512" class="Symbol">;</a> <a id="23514" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="23518" class="Symbol">;</a> <a id="23520" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="23524" class="Symbol">)</a> <a id="23526" class="Keyword">renaming</a> <a id="23535" class="Symbol">(</a><a id="23536" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="23542" class="Symbol">to</a> <a id="23545" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="23551" class="Symbol">)</a>
<a id="23553" class="Keyword">import</a> <a id="23560" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="23571" class="Keyword">using</a> <a id="23577" class="Symbol">(</a><a id="23578" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="23579" class="Symbol">;</a> <a id="23581" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="23587" class="Symbol">)</a>
<a id="23589" class="Keyword">import</a> <a id="23596" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html" class="Module">Function.Equivalence</a> <a id="23617" class="Keyword">using</a> <a id="23623" class="Symbol">(</a><a id="23624" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html#971" class="Function Operator">_⇔_</a><a id="23627" class="Symbol">)</a>
</pre>{% endraw %}The standard library constructs pairs with `_,_` whereas we use `⟨_,_⟩`.
The former makes it convenient to build triples or larger tuples from pairs,
permitting `a , b , c` to stand for `(a , (b , c))`.  But it conflicts with
other useful notations, such as `[_,_]` to construct a list of two elements in
Chapter [Lists]({{ site.baseurl }}/Lists/)
and `Γ , A` to extend environments in
Chapter [DeBruijn]({{ site.baseurl }}/DeBruijn/).
The standard library `_⇔_` is similar to ours, but the one in the
standard library is less convenient, since it is parameterised with
respect to an arbitrary notion of equivalence.


## Unicode

This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
