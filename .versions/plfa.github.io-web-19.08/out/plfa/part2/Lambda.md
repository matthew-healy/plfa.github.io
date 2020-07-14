---
src       : "src/plfa/part2/Lambda.lagda.md"
title     : "Lambda: Introduction to Lambda Calculus"
layout    : page
prev      : /Lists/
permalink : /Lambda/
next      : /Properties/
---

{% raw %}<pre class="Agda"><a id="151" class="Keyword">module</a> <a id="158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}" class="Module">plfa.part2.Lambda</a> <a id="176" class="Keyword">where</a>
</pre>{% endraw %}
The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It captures the key concept of
_functional abstraction_, which appears in pretty much every programming
language, in the form of either functions, procedures, or methods.
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo Plotkin's _Programmable Computable
Functions_ (PCF), and add operations on natural numbers and
recursive function definitions.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[Properties]({{ site.baseurl }}/Properties/)
proves its main properties, including
progress and preservation.  Following chapters will look at a number
of variants of lambda calculus.

Be aware that the approach we take here is _not_ our recommended
approach to formalisation.  Using de Bruijn indices and
intrinsically-typed terms, as we will do in
Chapter [DeBruijn]({{ site.baseurl }}/DeBruijn/),
leads to a more compact formulation.  Nonetheless, we begin with named
variables and extrinsically-typed terms,
partly because names are easier than indices to read,
and partly because the development is more traditional.

The development in this chapter was inspired by the corresponding
development in Chapter _Stlc_ of _Software Foundations_
(_Programming Language Foundations_).  We differ by
representing contexts explicitly (as lists pairing identifiers with
types) rather than as partial maps (which take identifiers to types),
which corresponds better to our subsequent development of DeBruijn
notation. We also differ by taking natural numbers as the base type
rather than booleans, allowing more sophisticated examples. In
particular, we will be able to show (twice!) that two plus two is
four.

## Imports

{% raw %}<pre class="Agda"><a id="2304" class="Keyword">open</a> <a id="2309" class="Keyword">import</a> <a id="2316" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="2354" class="Keyword">using</a> <a id="2360" class="Symbol">(</a><a id="2361" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="2364" class="Symbol">;</a> <a id="2366" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">_≢_</a><a id="2369" class="Symbol">;</a> <a id="2371" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="2375" class="Symbol">)</a>
<a id="2377" class="Keyword">open</a> <a id="2382" class="Keyword">import</a> <a id="2389" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.html" class="Module">Data.String</a> <a id="2401" class="Keyword">using</a> <a id="2407" class="Symbol">(</a><a id="2408" href="Agda.Builtin.String.html#206" class="Postulate">String</a><a id="2414" class="Symbol">;</a> <a id="2416" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">_≟_</a><a id="2419" class="Symbol">)</a>
<a id="2421" class="Keyword">open</a> <a id="2426" class="Keyword">import</a> <a id="2433" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="2442" class="Keyword">using</a> <a id="2448" class="Symbol">(</a><a id="2449" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="2450" class="Symbol">;</a> <a id="2452" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="2456" class="Symbol">;</a> <a id="2458" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="2461" class="Symbol">)</a>
<a id="2463" class="Keyword">open</a> <a id="2468" class="Keyword">import</a> <a id="2475" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="2486" class="Keyword">using</a> <a id="2492" class="Symbol">(</a><a id="2493" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="2494" class="Symbol">;</a> <a id="2496" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="2502" class="Symbol">)</a>
<a id="2504" class="Keyword">open</a> <a id="2509" class="Keyword">import</a> <a id="2516" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="2533" class="Keyword">using</a> <a id="2539" class="Symbol">(</a><a id="2540" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="2543" class="Symbol">;</a> <a id="2545" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="2548" class="Symbol">;</a> <a id="2550" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="2552" class="Symbol">;</a> <a id="2554" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="2556" class="Symbol">)</a>
<a id="2558" class="Keyword">open</a> <a id="2563" class="Keyword">import</a> <a id="2570" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.html" class="Module">Data.List</a> <a id="2580" class="Keyword">using</a> <a id="2586" class="Symbol">(</a><a id="2587" href="Agda.Builtin.List.html#121" class="Datatype">List</a><a id="2591" class="Symbol">;</a> <a id="2593" href="Agda.Builtin.List.html#173" class="InductiveConstructor Operator">_∷_</a><a id="2596" class="Symbol">;</a> <a id="2598" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.Base.html#8786" class="InductiveConstructor">[]</a><a id="2600" class="Symbol">)</a>
</pre>{% endraw %}
## Syntax of terms

Terms have seven constructs. Three are for the core lambda calculus:

  * Variables `` ` x ``
  * Abstractions `ƛ x ⇒ N`
  * Applications `L · M`

Three are for the naturals:

  * Zero `` `zero ``
  * Successor `` `suc ``
  * Case `` case L [zero⇒ M |suc x ⇒ N ] ``

And one is for recursion:

  * Fixpoint `μ x ⇒ M`

Abstraction is also called _lambda abstraction_, and is the construct
from which the calculus takes its name.

With the exception of variables and fixpoints, each term
form either constructs a value of a given type (abstractions yield functions,
zero and successor yield natural numbers) or deconstructs it (applications use functions,
case terms use naturals). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in Backus-Naur Form (BNF):

    L, M, N  ::=
      ` x  |  ƛ x ⇒ N  |  L · M  |
      `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
      μ x ⇒ M

And here it is formalised in Agda:
{% raw %}<pre class="Agda"><a id="Id"></a><a id="3695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3695" class="Function">Id</a> <a id="3698" class="Symbol">:</a> <a id="3700" class="PrimitiveType">Set</a>
<a id="3704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3695" class="Function">Id</a> <a id="3707" class="Symbol">=</a> <a id="3709" href="Agda.Builtin.String.html#206" class="Postulate">String</a>

<a id="3717" class="Keyword">infix</a>  <a id="3724" class="Number">5</a>  <a id="3727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ_⇒_</a>
<a id="3732" class="Keyword">infix</a>  <a id="3739" class="Number">5</a>  <a id="3742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ_⇒_</a>
<a id="3747" class="Keyword">infixl</a> <a id="3754" class="Number">7</a>  <a id="3757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33752" class="InductiveConstructor Operator">_·_</a>
<a id="3761" class="Keyword">infix</a>  <a id="3768" class="Number">8</a>  <a id="3771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc_</a>
<a id="3777" class="Keyword">infix</a>  <a id="3784" class="Number">9</a>  <a id="3787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`_</a>

<a id="3791" class="Keyword">data</a> <a id="Term"></a><a id="3796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3796" class="Datatype">Term</a> <a id="3801" class="Symbol">:</a> <a id="3803" class="PrimitiveType">Set</a> <a id="3807" class="Keyword">where</a>
  <a id="Term.`_"></a><a id="3815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`_</a>                      <a id="3839" class="Symbol">:</a>  <a id="3842" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="3845" class="Symbol">→</a> <a id="3847" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.ƛ_⇒_"></a><a id="3854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ_⇒_</a>                    <a id="3878" class="Symbol">:</a>  <a id="3881" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="3884" class="Symbol">→</a> <a id="3886" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="3891" class="Symbol">→</a> <a id="3893" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term._·_"></a><a id="3900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">_·_</a>                     <a id="3924" class="Symbol">:</a>  <a id="3927" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="3932" class="Symbol">→</a> <a id="3934" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="3939" class="Symbol">→</a> <a id="3941" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.`zero"></a><a id="3948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3948" class="InductiveConstructor">`zero</a>                   <a id="3972" class="Symbol">:</a>  <a id="3975" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.`suc_"></a><a id="3982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc_</a>                   <a id="4006" class="Symbol">:</a>  <a id="4009" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4014" class="Symbol">→</a> <a id="4016" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.case_[zero⇒_|suc_⇒_]"></a><a id="4023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case_[zero⇒_|suc_⇒_]</a>    <a id="4047" class="Symbol">:</a>  <a id="4050" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4055" class="Symbol">→</a> <a id="4057" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4062" class="Symbol">→</a> <a id="4064" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="4067" class="Symbol">→</a> <a id="4069" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4074" class="Symbol">→</a> <a id="4076" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.μ_⇒_"></a><a id="4083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ_⇒_</a>                    <a id="4107" class="Symbol">:</a>  <a id="4110" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="4113" class="Symbol">→</a> <a id="4115" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4120" class="Symbol">→</a> <a id="4122" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
</pre>{% endraw %}We represent identifiers by strings.  We choose precedence so that
lambda abstraction and fixpoint bind least tightly, then application,
then successor, and tightest of all is the constructor for variables.
Case expressions are self-bracketing.


### Example terms

Here are some example terms: the natural number two,
a function that adds naturals,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="two"></a><a id="4524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4524" class="Function">two</a> <a id="4528" class="Symbol">:</a> <a id="4530" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="4535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4524" class="Function">two</a> <a id="4539" class="Symbol">=</a> <a id="4541" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="4546" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="4551" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>

<a id="plus"></a><a id="4558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4558" class="Function">plus</a> <a id="4563" class="Symbol">:</a> <a id="4565" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="4570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4558" class="Function">plus</a> <a id="4575" class="Symbol">=</a> <a id="4577" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="4579" class="String">&quot;+&quot;</a> <a id="4583" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="4585" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="4587" class="String">&quot;m&quot;</a> <a id="4591" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="4593" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="4595" class="String">&quot;n&quot;</a> <a id="4599" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
         <a id="4610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="4615" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4617" class="String">&quot;m&quot;</a>
           <a id="4632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="4639" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4641" class="String">&quot;n&quot;</a>
           <a id="4656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">|suc</a> <a id="4661" class="String">&quot;m&quot;</a> <a id="4665" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="4667" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="4672" class="Symbol">(</a><a id="4673" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4675" class="String">&quot;+&quot;</a> <a id="4679" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="4681" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4683" class="String">&quot;m&quot;</a> <a id="4687" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="4689" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4691" class="String">&quot;n&quot;</a><a id="4694" class="Symbol">)</a> <a id="4696" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
</pre>{% endraw %}The recursive definition of addition is similar to our original
definition of `_+_` for naturals, as given in
Chapter [Naturals]({{ site.baseurl }}/Naturals/#plus).
Here variable "m" is bound twice, once in a lambda abstraction and once in
the successor branch of the case; the first use of "m" refers to
the former and the second to the latter.  Any use of "m" in the successor branch
must refer to the latter binding, and so we say that the latter binding _shadows_
the former.  Later we will confirm that two plus two is four, in other words that
the term

    plus · two · two

reduces to `` `suc `suc `suc `suc `zero ``.

As a second example, we use higher-order functions to represent
natural numbers.  In particular, the number _n_ is represented by a
function that accepts two arguments and applies the first _n_ times to the
second.  This is called the _Church representation_ of the
naturals.  Here are some example terms: the Church numeral two, a
function that adds Church numerals, a function to compute successor,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="twoᶜ"></a><a id="5773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="5778" class="Symbol">:</a> <a id="5780" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="5785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="5790" class="Symbol">=</a>  <a id="5793" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5795" class="String">&quot;s&quot;</a> <a id="5799" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5801" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5803" class="String">&quot;z&quot;</a> <a id="5807" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5809" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5811" class="String">&quot;s&quot;</a> <a id="5815" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5817" class="Symbol">(</a><a id="5818" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5820" class="String">&quot;s&quot;</a> <a id="5824" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5826" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5828" class="String">&quot;z&quot;</a><a id="5831" class="Symbol">)</a>

<a id="plusᶜ"></a><a id="5834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5834" class="Function">plusᶜ</a> <a id="5840" class="Symbol">:</a> <a id="5842" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="5847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5834" class="Function">plusᶜ</a> <a id="5853" class="Symbol">=</a>  <a id="5856" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5858" class="String">&quot;m&quot;</a> <a id="5862" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5864" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5866" class="String">&quot;n&quot;</a> <a id="5870" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5872" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5874" class="String">&quot;s&quot;</a> <a id="5878" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5880" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5882" class="String">&quot;z&quot;</a> <a id="5886" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
         <a id="5897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="5899" class="String">&quot;m&quot;</a> <a id="5903" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5905" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5907" class="String">&quot;s&quot;</a> <a id="5911" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5913" class="Symbol">(</a><a id="5914" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5916" class="String">&quot;n&quot;</a> <a id="5920" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5922" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5924" class="String">&quot;s&quot;</a> <a id="5928" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5930" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5932" class="String">&quot;z&quot;</a><a id="5935" class="Symbol">)</a>

<a id="sucᶜ"></a><a id="5938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="5943" class="Symbol">:</a> <a id="5945" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="5950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="5955" class="Symbol">=</a> <a id="5957" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5959" class="String">&quot;n&quot;</a> <a id="5963" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5965" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="5970" class="Symbol">(</a><a id="5971" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5973" class="String">&quot;n&quot;</a><a id="5976" class="Symbol">)</a>
</pre>{% endraw %}The Church numeral for two takes two arguments `s` and `z`
and applies `s` twice to `z`.
Addition takes two numerals `m` and `n`, a
function `s` and an argument `z`, and it uses `m` to apply `s` to the
result of using `n` to apply `s` to `z`; hence `s` is applied `m` plus
`n` times to `z`, yielding the Church numeral for the sum of `m` and
`n`.  For convenience, we define a function that computes successor.
To convert a Church numeral to the corresponding natural, we apply
it to the `sucᶜ` function and the natural number zero.
Again, later we will confirm that two plus two is four,
in other words that the term

    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

reduces to `` `suc `suc `suc `suc `zero ``.


#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.

{% raw %}<pre class="Agda"><a id="6858" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ` (practice)

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

{% raw %}<pre class="Agda"><a id="7139" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `primed` (stretch)

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="7373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7373" class="Function Operator">ƛ′_⇒_</a> <a id="7379" class="Symbol">:</a> <a id="7381" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7386" class="Symbol">→</a> <a id="7388" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7393" class="Symbol">→</a> <a id="7395" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="7400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7373" class="Function Operator">ƛ′</a> <a id="7403" class="Symbol">(</a><a id="7404" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="7406" href="plfa.part2.Lambda.html#7406" class="Bound">x</a><a id="7407" class="Symbol">)</a> <a id="7409" href="plfa.part2.Lambda.html#7373" class="Function Operator">⇒</a> <a id="7411" href="plfa.part2.Lambda.html#7411" class="Bound">N</a>  <a id="7414" class="Symbol">=</a>  <a id="7417" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="7419" href="plfa.part2.Lambda.html#7406" class="Bound">x</a> <a id="7421" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="7423" href="plfa.part2.Lambda.html#7411" class="Bound">N</a>
<a id="7425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7373" class="CatchallClause Function Operator">ƛ′</a><a id="7427" class="CatchallClause"> </a><a id="7428" class="CatchallClause Symbol">_</a><a id="7429" class="CatchallClause"> </a><a id="7430" href="plfa.part2.Lambda.html#7373" class="CatchallClause Function Operator">⇒</a><a id="7431" class="CatchallClause"> </a><a id="7432" class="CatchallClause Symbol">_</a>      <a id="7439" class="Symbol">=</a>  <a id="7442" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7449" href="plfa.part2.Lambda.html#7478" class="Postulate">impossible</a>
  <a id="7462" class="Keyword">where</a> <a id="7468" class="Keyword">postulate</a> <a id="7478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7478" class="Postulate">impossible</a> <a id="7489" class="Symbol">:</a> <a id="7491" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="7494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7494" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="7516" class="Symbol">:</a> <a id="7518" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7523" class="Symbol">→</a> <a id="7525" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7530" class="Symbol">→</a> <a id="7532" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7537" class="Symbol">→</a> <a id="7539" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7544" class="Symbol">→</a> <a id="7546" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="7551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7494" class="Function Operator">case′</a> <a id="7557" href="plfa.part2.Lambda.html#7557" class="Bound">L</a> <a id="7559" href="plfa.part2.Lambda.html#7494" class="Function Operator">[zero⇒</a> <a id="7566" href="plfa.part2.Lambda.html#7566" class="Bound">M</a> <a id="7568" href="plfa.part2.Lambda.html#7494" class="Function Operator">|suc</a> <a id="7573" class="Symbol">(</a><a id="7574" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="7576" href="plfa.part2.Lambda.html#7576" class="Bound">x</a><a id="7577" class="Symbol">)</a> <a id="7579" href="plfa.part2.Lambda.html#7494" class="Function Operator">⇒</a> <a id="7581" href="plfa.part2.Lambda.html#7581" class="Bound">N</a> <a id="7583" href="plfa.part2.Lambda.html#7494" class="Function Operator">]</a>  <a id="7586" class="Symbol">=</a>  <a id="7589" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="7594" href="plfa.part2.Lambda.html#7557" class="Bound">L</a> <a id="7596" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="7603" href="plfa.part2.Lambda.html#7566" class="Bound">M</a> <a id="7605" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="7610" href="plfa.part2.Lambda.html#7576" class="Bound">x</a> <a id="7612" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="7614" href="plfa.part2.Lambda.html#7581" class="Bound">N</a> <a id="7616" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="7618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7494" class="CatchallClause Function Operator">case′</a><a id="7623" class="CatchallClause"> </a><a id="7624" class="CatchallClause Symbol">_</a><a id="7625" class="CatchallClause"> </a><a id="7626" href="plfa.part2.Lambda.html#7494" class="CatchallClause Function Operator">[zero⇒</a><a id="7632" class="CatchallClause"> </a><a id="7633" class="CatchallClause Symbol">_</a><a id="7634" class="CatchallClause"> </a><a id="7635" href="plfa.part2.Lambda.html#7494" class="CatchallClause Function Operator">|suc</a><a id="7639" class="CatchallClause"> </a><a id="7640" class="CatchallClause Symbol">_</a><a id="7641" class="CatchallClause"> </a><a id="7642" href="plfa.part2.Lambda.html#7494" class="CatchallClause Function Operator">⇒</a><a id="7643" class="CatchallClause"> </a><a id="7644" class="CatchallClause Symbol">_</a><a id="7645" class="CatchallClause"> </a><a id="7646" href="plfa.part2.Lambda.html#7494" class="CatchallClause Function Operator">]</a>      <a id="7653" class="Symbol">=</a>  <a id="7656" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7663" href="plfa.part2.Lambda.html#7692" class="Postulate">impossible</a>
  <a id="7676" class="Keyword">where</a> <a id="7682" class="Keyword">postulate</a> <a id="7692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7692" class="Postulate">impossible</a> <a id="7703" class="Symbol">:</a> <a id="7705" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="7708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7708" class="Function Operator">μ′_⇒_</a> <a id="7714" class="Symbol">:</a> <a id="7716" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7721" class="Symbol">→</a> <a id="7723" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7728" class="Symbol">→</a> <a id="7730" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="7735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7708" class="Function Operator">μ′</a> <a id="7738" class="Symbol">(</a><a id="7739" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="7741" href="plfa.part2.Lambda.html#7741" class="Bound">x</a><a id="7742" class="Symbol">)</a> <a id="7744" href="plfa.part2.Lambda.html#7708" class="Function Operator">⇒</a> <a id="7746" href="plfa.part2.Lambda.html#7746" class="Bound">N</a>  <a id="7749" class="Symbol">=</a>  <a id="7752" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="7754" href="plfa.part2.Lambda.html#7741" class="Bound">x</a> <a id="7756" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="7758" href="plfa.part2.Lambda.html#7746" class="Bound">N</a>
<a id="7760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7708" class="CatchallClause Function Operator">μ′</a><a id="7762" class="CatchallClause"> </a><a id="7763" class="CatchallClause Symbol">_</a><a id="7764" class="CatchallClause"> </a><a id="7765" href="plfa.part2.Lambda.html#7708" class="CatchallClause Function Operator">⇒</a><a id="7766" class="CatchallClause"> </a><a id="7767" class="CatchallClause Symbol">_</a>      <a id="7774" class="Symbol">=</a>  <a id="7777" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7784" href="plfa.part2.Lambda.html#7813" class="Postulate">impossible</a>
  <a id="7797" class="Keyword">where</a> <a id="7803" class="Keyword">postulate</a> <a id="7813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7813" class="Postulate">impossible</a> <a id="7824" class="Symbol">:</a> <a id="7826" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}The definition of `plus` can now be written as follows:
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="7892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7892" class="Function">plus′</a> <a id="7898" class="Symbol">:</a> <a id="7900" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="7905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7892" class="Function">plus′</a> <a id="7911" class="Symbol">=</a> <a id="7913" href="plfa.part2.Lambda.html#7708" class="Function Operator">μ′</a> <a id="7916" href="plfa.part2.Lambda.html#8023" class="Function">+</a> <a id="7918" href="plfa.part2.Lambda.html#7708" class="Function Operator">⇒</a> <a id="7920" href="plfa.part2.Lambda.html#7373" class="Function Operator">ƛ′</a> <a id="7923" href="plfa.part2.Lambda.html#8037" class="Function">m</a> <a id="7925" href="plfa.part2.Lambda.html#7373" class="Function Operator">⇒</a> <a id="7927" href="plfa.part2.Lambda.html#7373" class="Function Operator">ƛ′</a> <a id="7930" href="plfa.part2.Lambda.html#8051" class="Function">n</a> <a id="7932" href="plfa.part2.Lambda.html#7373" class="Function Operator">⇒</a>
          <a id="7944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7494" class="Function Operator">case′</a> <a id="7950" href="plfa.part2.Lambda.html#8037" class="Function">m</a>
            <a id="7964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7494" class="Function Operator">[zero⇒</a> <a id="7971" href="plfa.part2.Lambda.html#8051" class="Function">n</a>
            <a id="7985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7494" class="Function Operator">|suc</a> <a id="7990" href="plfa.part2.Lambda.html#8037" class="Function">m</a> <a id="7992" href="plfa.part2.Lambda.html#7494" class="Function Operator">⇒</a> <a id="7994" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="7999" class="Symbol">(</a><a id="8000" href="plfa.part2.Lambda.html#8023" class="Function">+</a> <a id="8002" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="8004" href="plfa.part2.Lambda.html#8037" class="Function">m</a> <a id="8006" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="8008" href="plfa.part2.Lambda.html#8051" class="Function">n</a><a id="8009" class="Symbol">)</a> <a id="8011" href="plfa.part2.Lambda.html#7494" class="Function Operator">]</a>
  <a id="8015" class="Keyword">where</a>
  <a id="8023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8023" class="Function">+</a>  <a id="8026" class="Symbol">=</a>  <a id="8029" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="8031" class="String">&quot;+&quot;</a>
  <a id="8037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8037" class="Function">m</a>  <a id="8040" class="Symbol">=</a>  <a id="8043" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="8045" class="String">&quot;m&quot;</a>
  <a id="8051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8051" class="Function">n</a>  <a id="8054" class="Symbol">=</a>  <a id="8057" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="8059" class="String">&quot;n&quot;</a>
</pre>{% endraw %}Write out the definition of multiplication in the same style.


### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.

Similarly, informal presentation often use the same notation for
function types, lambda abstraction, and function application in both
the _object language_ (the language one is describing) and the
_meta-language_ (the language in which the description is written),
trusting readers can use context to distinguish the two.  Agda is
not quite so forgiving, so here we use `ƛ x ⇒ N` and `L · M` for the
object language, as compared to `λ x → N` and `L M` in our
meta-language, Agda.


### Bound and free variables

In an abstraction `ƛ x ⇒ N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  A central feature
of lambda calculus is that consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x") ``
* `` ƛ "sam" ⇒ ƛ "zelda" ⇒ ` "sam" · (` "sam" · ` "zelda") ``
* `` ƛ "z" ⇒ ƛ "s" ⇒ ` "z" · (` "z" · ` "s") ``
* `` ƛ "😇" ⇒ ƛ "😈" ⇒ ` "😇" · (` "😇" · ` "😈" ) ``

are all considered equivalent.  Following the convention introduced
by Haskell Curry, who used the Greek letter `α` (_alpha_) to label such rules,
this equivalence relation is called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms:

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as bound variables.

* `` ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has `z` bound and `s` free.

* `` ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  We will focus on reduction of closed terms.

Different occurrences of a variable may be bound and free.
In the term

    (ƛ "x" ⇒ ` "x") · ` "x"

the inner occurrence of `x` is bound while the outer occurrence is free.
By alpha renaming, the term above is equivalent to

    (ƛ "y" ⇒ ` "y") · ` "x"

in which `y` is bound and `x` is free.  A common convention, called the
_Barendregt convention_, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

Case and recursion also introduce bound variables, which are also subject
to alpha renaming. In the term

    μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

notice that there are two binding occurrences of `m`, one in the first
line and one in the last line.  It is equivalent to the following term,

    μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
      case ` "x"
        [zero⇒ ` "y"
        |suc "x′" ⇒ `suc (` "plus" · ` "x′" · ` "y") ]

where the two binding occurrences corresponding to `m` now have distinct
names, `x` and `x′`.


## Values

A _value_ is a term that corresponds to an answer.
Thus, `` `suc `suc `suc `suc `zero `` is a value,
while `` plus · two · two `` is not.
Following convention, we treat all function abstractions
as values; thus, `` plus `` by itself is considered a value.

The predicate `Value M` holds if term `M` is a value:

{% raw %}<pre class="Agda"><a id="11590" class="Keyword">data</a> <a id="Value"></a><a id="11595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11595" class="Datatype">Value</a> <a id="11601" class="Symbol">:</a> <a id="11603" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="11608" class="Symbol">→</a> <a id="11610" class="PrimitiveType">Set</a> <a id="11614" class="Keyword">where</a>

  <a id="Value.V-ƛ"></a><a id="11623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11623" class="InductiveConstructor">V-ƛ</a> <a id="11627" class="Symbol">:</a> <a id="11629" class="Symbol">∀</a> <a id="11631" class="Symbol">{</a><a id="11632" href="plfa.part2.Lambda.html#11632" class="Bound">x</a> <a id="11634" href="plfa.part2.Lambda.html#11634" class="Bound">N</a><a id="11635" class="Symbol">}</a>
      <a id="11643" class="Comment">---------------</a>
    <a id="11663" class="Symbol">→</a> <a id="11665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11595" class="Datatype">Value</a> <a id="11671" class="Symbol">(</a><a id="11672" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="11674" href="plfa.part2.Lambda.html#11632" class="Bound">x</a> <a id="11676" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="11678" href="plfa.part2.Lambda.html#11634" class="Bound">N</a><a id="11679" class="Symbol">)</a>

  <a id="Value.V-zero"></a><a id="11684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11684" class="InductiveConstructor">V-zero</a> <a id="11691" class="Symbol">:</a>
      <a id="11699" class="Comment">-----------</a>
      <a id="11717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11595" class="Datatype">Value</a> <a id="11723" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>

  <a id="Value.V-suc"></a><a id="11732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11732" class="InductiveConstructor">V-suc</a> <a id="11738" class="Symbol">:</a> <a id="11740" class="Symbol">∀</a> <a id="11742" class="Symbol">{</a><a id="11743" href="plfa.part2.Lambda.html#11743" class="Bound">V</a><a id="11744" class="Symbol">}</a>
    <a id="11750" class="Symbol">→</a> <a id="11752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11595" class="Datatype">Value</a> <a id="11758" href="plfa.part2.Lambda.html#11743" class="Bound">V</a>
      <a id="11766" class="Comment">--------------</a>
    <a id="11785" class="Symbol">→</a> <a id="11787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11595" class="Datatype">Value</a> <a id="11793" class="Symbol">(</a><a id="11794" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="11799" href="plfa.part2.Lambda.html#11743" class="Bound">V</a><a id="11800" class="Symbol">)</a>
</pre>{% endraw %}
In what follows, we let `V` and `W` range over values.


### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`ƛ x ⇒ N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
We consider this approach in
Chapter [Untyped]({{ site.baseurl }}/Untyped/).


## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · sucᶜ · `zero
    —→
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · "z")) · `zero
    —→
      sucᶜ · (sucᶜ · `zero)

where we substitute `sucᶜ` for `` ` "s" `` and `` `zero `` for `` ` "z" ``
in the body of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`",
or equivalently, "in `N` replace `x` by `V`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since in fact we
usually substitute values.

Here are some examples:

* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``.
* `` (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] `` yields
  `` sucᶜ · (sucᶜ · `zero) ``.
* `` (ƛ "x" ⇒ ` "y") [ "y" := `zero ] `` yields `` ƛ "x" ⇒ `zero ``.
* `` (ƛ "x" ⇒ ` "x") [ "x" := `zero ] `` yields `` ƛ "x" ⇒ ` "x" ``.
* `` (ƛ "y" ⇒ ` "y") [ "x" := `zero ] `` yields `` ƛ "y" ⇒ ` "y" ``.

In the last but one example, substituting `` `zero `` for `x` in
`` ƛ "x" ⇒ ` "x" `` does _not_ yield `` ƛ "x" ⇒ `zero ``,
since `x` is bound in the lambda abstraction.
The choice of bound names is irrelevant: both
`` ƛ "x" ⇒ ` "x" `` and `` ƛ "y" ⇒ ` "y" `` stand for the
identity function.  One way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they just happen to have the same name.

We will give a definition of substitution that is only valid
when term substituted for the variable is closed. This is because
substitution by terms that are _not_ closed may require renaming
of bound variables. For example:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] `` should not yield <br/>
  `` (ƛ "x" ⇒ ` "x" · (` "x" · `zero)) ``.

Instead, we should rename the bound variable to avoid capture:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield <br/>
  `` ƛ "x′" ⇒ ` "x′" · (` "x" · `zero) ``.

Here `x′` is a fresh variable distinct from `x`.
Formal definition of substitution with suitable renaming is considerably
more complex, so we avoid it by restricting to substitution by closed terms,
which will be adequate for our purposes.

Here is the formal definition of substitution by closed terms in Agda:

{% raw %}<pre class="Agda"><a id="14961" class="Keyword">infix</a> <a id="14967" class="Number">9</a> <a id="14969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#14978" class="Function Operator">_[_:=_]</a>

<a id="_[_:=_]"></a><a id="14978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#14978" class="Function Operator">_[_:=_]</a> <a id="14986" class="Symbol">:</a> <a id="14988" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="14993" class="Symbol">→</a> <a id="14995" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="14998" class="Symbol">→</a> <a id="15000" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="15005" class="Symbol">→</a> <a id="15007" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="15012" class="Symbol">(</a><a id="15013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="15015" href="plfa.part2.Lambda.html#15015" class="Bound">x</a><a id="15016" class="Symbol">)</a> <a id="15018" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15020" href="plfa.part2.Lambda.html#15020" class="Bound">y</a> <a id="15022" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15025" href="plfa.part2.Lambda.html#15025" class="Bound">V</a> <a id="15027" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15029" class="Keyword">with</a> <a id="15034" href="plfa.part2.Lambda.html#15015" class="Bound">x</a> <a id="15036" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15038" href="plfa.part2.Lambda.html#15020" class="Bound">y</a>
<a id="15040" class="Symbol">...</a> <a id="15044" class="Symbol">|</a> <a id="15046" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15050" class="Symbol">_</a>          <a id="15061" class="Symbol">=</a>  <a id="15064" class="Bound">V</a>
<a id="15066" class="Symbol">...</a> <a id="15070" class="Symbol">|</a> <a id="15072" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15076" class="Symbol">_</a>          <a id="15087" class="Symbol">=</a>  <a id="15090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="15092" class="Bound">x</a>
<a id="15094" class="Symbol">(</a><a id="15095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15097" href="plfa.part2.Lambda.html#15097" class="Bound">x</a> <a id="15099" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15101" href="plfa.part2.Lambda.html#15101" class="Bound">N</a><a id="15102" class="Symbol">)</a> <a id="15104" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15106" href="plfa.part2.Lambda.html#15106" class="Bound">y</a> <a id="15108" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15111" href="plfa.part2.Lambda.html#15111" class="Bound">V</a> <a id="15113" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15115" class="Keyword">with</a> <a id="15120" href="plfa.part2.Lambda.html#15097" class="Bound">x</a> <a id="15122" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15124" href="plfa.part2.Lambda.html#15106" class="Bound">y</a>
<a id="15126" class="Symbol">...</a> <a id="15130" class="Symbol">|</a> <a id="15132" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15136" class="Symbol">_</a>          <a id="15147" class="Symbol">=</a>  <a id="15150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15152" class="Bound">x</a> <a id="15154" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15156" class="Bound">N</a>
<a id="15158" class="Symbol">...</a> <a id="15162" class="Symbol">|</a> <a id="15164" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15168" class="Symbol">_</a>          <a id="15179" class="Symbol">=</a>  <a id="15182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15184" class="Bound">x</a> <a id="15186" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15188" class="Bound">N</a> <a id="15190" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15192" class="Bound">y</a> <a id="15194" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15197" class="Bound">V</a> <a id="15199" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>
<a id="15201" class="Symbol">(</a><a id="15202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15202" class="Bound">L</a> <a id="15204" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="15206" href="plfa.part2.Lambda.html#15206" class="Bound">M</a><a id="15207" class="Symbol">)</a> <a id="15209" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15211" href="plfa.part2.Lambda.html#15211" class="Bound">y</a> <a id="15213" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15216" href="plfa.part2.Lambda.html#15216" class="Bound">V</a> <a id="15218" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>   <a id="15222" class="Symbol">=</a>  <a id="15225" href="plfa.part2.Lambda.html#15202" class="Bound">L</a> <a id="15227" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15229" href="plfa.part2.Lambda.html#15211" class="Bound">y</a> <a id="15231" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15234" href="plfa.part2.Lambda.html#15216" class="Bound">V</a> <a id="15236" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15238" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="15240" href="plfa.part2.Lambda.html#15206" class="Bound">M</a> <a id="15242" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15244" href="plfa.part2.Lambda.html#15211" class="Bound">y</a> <a id="15246" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15249" href="plfa.part2.Lambda.html#15216" class="Bound">V</a> <a id="15251" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>
<a id="15253" class="Symbol">(</a><a id="15254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3948" class="InductiveConstructor">`zero</a><a id="15259" class="Symbol">)</a> <a id="15261" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15263" href="plfa.part2.Lambda.html#15263" class="Bound">y</a> <a id="15265" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15268" href="plfa.part2.Lambda.html#15268" class="Bound">V</a> <a id="15270" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>   <a id="15274" class="Symbol">=</a>  <a id="15277" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="15283" class="Symbol">(</a><a id="15284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="15289" href="plfa.part2.Lambda.html#15289" class="Bound">M</a><a id="15290" class="Symbol">)</a> <a id="15292" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15294" href="plfa.part2.Lambda.html#15294" class="Bound">y</a> <a id="15296" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15299" href="plfa.part2.Lambda.html#15299" class="Bound">V</a> <a id="15301" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>  <a id="15304" class="Symbol">=</a>  <a id="15307" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="15312" href="plfa.part2.Lambda.html#15289" class="Bound">M</a> <a id="15314" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15316" href="plfa.part2.Lambda.html#15294" class="Bound">y</a> <a id="15318" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15321" href="plfa.part2.Lambda.html#15299" class="Bound">V</a> <a id="15323" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>
<a id="15325" class="Symbol">(</a><a id="15326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="15331" href="plfa.part2.Lambda.html#15331" class="Bound">L</a> <a id="15333" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="15340" href="plfa.part2.Lambda.html#15340" class="Bound">M</a> <a id="15342" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="15347" href="plfa.part2.Lambda.html#15347" class="Bound">x</a> <a id="15349" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="15351" href="plfa.part2.Lambda.html#15351" class="Bound">N</a> <a id="15353" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="15354" class="Symbol">)</a> <a id="15356" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15358" href="plfa.part2.Lambda.html#15358" class="Bound">y</a> <a id="15360" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15363" href="plfa.part2.Lambda.html#15363" class="Bound">V</a> <a id="15365" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15367" class="Keyword">with</a> <a id="15372" href="plfa.part2.Lambda.html#15347" class="Bound">x</a> <a id="15374" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15376" href="plfa.part2.Lambda.html#15358" class="Bound">y</a>
<a id="15378" class="Symbol">...</a> <a id="15382" class="Symbol">|</a> <a id="15384" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15388" class="Symbol">_</a>          <a id="15399" class="Symbol">=</a>  <a id="15402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="15407" class="Bound">L</a> <a id="15409" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15411" class="Bound">y</a> <a id="15413" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15416" class="Bound">V</a> <a id="15418" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15420" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="15427" class="Bound">M</a> <a id="15429" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15431" class="Bound">y</a> <a id="15433" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15436" class="Bound">V</a> <a id="15438" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15440" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="15445" class="Bound">x</a> <a id="15447" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="15449" class="Bound">N</a> <a id="15451" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="15453" class="Symbol">...</a> <a id="15457" class="Symbol">|</a> <a id="15459" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15463" class="Symbol">_</a>          <a id="15474" class="Symbol">=</a>  <a id="15477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="15482" class="Bound">L</a> <a id="15484" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15486" class="Bound">y</a> <a id="15488" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15491" class="Bound">V</a> <a id="15493" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15495" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="15502" class="Bound">M</a> <a id="15504" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15506" class="Bound">y</a> <a id="15508" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15511" class="Bound">V</a> <a id="15513" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15515" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="15520" class="Bound">x</a> <a id="15522" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="15524" class="Bound">N</a> <a id="15526" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15528" class="Bound">y</a> <a id="15530" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15533" class="Bound">V</a> <a id="15535" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15537" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="15539" class="Symbol">(</a><a id="15540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="15542" href="plfa.part2.Lambda.html#15542" class="Bound">x</a> <a id="15544" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="15546" href="plfa.part2.Lambda.html#15546" class="Bound">N</a><a id="15547" class="Symbol">)</a> <a id="15549" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15551" href="plfa.part2.Lambda.html#15551" class="Bound">y</a> <a id="15553" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15556" href="plfa.part2.Lambda.html#15556" class="Bound">V</a> <a id="15558" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="15560" class="Keyword">with</a> <a id="15565" href="plfa.part2.Lambda.html#15542" class="Bound">x</a> <a id="15567" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15569" href="plfa.part2.Lambda.html#15551" class="Bound">y</a>
<a id="15571" class="Symbol">...</a> <a id="15575" class="Symbol">|</a> <a id="15577" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15581" class="Symbol">_</a>          <a id="15592" class="Symbol">=</a>  <a id="15595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="15597" class="Bound">x</a> <a id="15599" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="15601" class="Bound">N</a>
<a id="15603" class="Symbol">...</a> <a id="15607" class="Symbol">|</a> <a id="15609" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15613" class="Symbol">_</a>          <a id="15624" class="Symbol">=</a>  <a id="15627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="15629" class="Bound">x</a> <a id="15631" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="15633" class="Bound">N</a> <a id="15635" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="15637" class="Bound">y</a> <a id="15639" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="15642" class="Bound">V</a> <a id="15644" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>
</pre>{% endraw %}
Let's unpack the first three cases:

* For variables, we compare `y`, the substituted variable,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `y`, the substituted variable,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we substitute inside the body.

* For application, we recursively substitute in the function
and the argument.

Case expressions and recursion also have bound variables that are
treated similarly to those in lambda abstractions.  Otherwise we
simply push substitution recursively into the subterms.


### Examples

Here is confirmation that the examples above are correct:

{% raw %}<pre class="Agda"><a id="16411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16411" class="Function">_</a> <a id="16413" class="Symbol">:</a> <a id="16415" class="Symbol">(</a><a id="16416" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16418" class="String">&quot;z&quot;</a> <a id="16422" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="16424" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16426" class="String">&quot;s&quot;</a> <a id="16430" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="16432" class="Symbol">(</a><a id="16433" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16435" class="String">&quot;s&quot;</a> <a id="16439" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="16441" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16443" class="String">&quot;z&quot;</a><a id="16446" class="Symbol">))</a> <a id="16449" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="16451" class="String">&quot;s&quot;</a> <a id="16455" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="16458" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="16463" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="16465" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16467" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16469" class="String">&quot;z&quot;</a> <a id="16473" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="16475" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="16480" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="16482" class="Symbol">(</a><a id="16483" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="16488" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="16490" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16492" class="String">&quot;z&quot;</a><a id="16495" class="Symbol">)</a>
<a id="16497" class="Symbol">_</a> <a id="16499" class="Symbol">=</a> <a id="16501" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16507" class="Function">_</a> <a id="16509" class="Symbol">:</a> <a id="16511" class="Symbol">(</a><a id="16512" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="16517" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="16519" class="Symbol">(</a><a id="16520" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="16525" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="16527" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16529" class="String">&quot;z&quot;</a><a id="16532" class="Symbol">))</a> <a id="16535" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="16537" class="String">&quot;z&quot;</a> <a id="16541" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="16544" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="16550" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="16552" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16554" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="16559" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="16561" class="Symbol">(</a><a id="16562" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="16567" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="16569" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="16574" class="Symbol">)</a>
<a id="16576" class="Symbol">_</a> <a id="16578" class="Symbol">=</a> <a id="16580" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16586" class="Function">_</a> <a id="16588" class="Symbol">:</a> <a id="16590" class="Symbol">(</a><a id="16591" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16593" class="String">&quot;x&quot;</a> <a id="16597" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="16599" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16601" class="String">&quot;y&quot;</a><a id="16604" class="Symbol">)</a> <a id="16606" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="16608" class="String">&quot;y&quot;</a> <a id="16612" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="16615" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="16621" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="16623" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16625" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16627" class="String">&quot;x&quot;</a> <a id="16631" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="16633" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="16639" class="Symbol">_</a> <a id="16641" class="Symbol">=</a> <a id="16643" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16649" class="Function">_</a> <a id="16651" class="Symbol">:</a> <a id="16653" class="Symbol">(</a><a id="16654" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16656" class="String">&quot;x&quot;</a> <a id="16660" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="16662" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16664" class="String">&quot;x&quot;</a><a id="16667" class="Symbol">)</a> <a id="16669" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="16671" class="String">&quot;x&quot;</a> <a id="16675" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="16678" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="16684" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="16686" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16688" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16690" class="String">&quot;x&quot;</a> <a id="16694" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="16696" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16698" class="String">&quot;x&quot;</a>
<a id="16702" class="Symbol">_</a> <a id="16704" class="Symbol">=</a> <a id="16706" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16712" class="Function">_</a> <a id="16714" class="Symbol">:</a> <a id="16716" class="Symbol">(</a><a id="16717" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16719" class="String">&quot;y&quot;</a> <a id="16723" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="16725" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16727" class="String">&quot;y&quot;</a><a id="16730" class="Symbol">)</a> <a id="16732" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="16734" class="String">&quot;x&quot;</a> <a id="16738" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="16741" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="16747" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a> <a id="16749" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16751" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16753" class="String">&quot;y&quot;</a> <a id="16757" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="16759" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16761" class="String">&quot;y&quot;</a>
<a id="16765" class="Symbol">_</a> <a id="16767" class="Symbol">=</a> <a id="16769" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}

#### Quiz

What is the result of the following substitution?

    (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]

1. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) ``
2. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ `zero)) ``
3. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")) ``
4. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ `zero)) ``


#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

{% raw %}<pre class="Agda"><a id="17392" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.

In an informal presentation of the operational semantics,
the rules for reduction of applications are written as follows:

    L —→ L′
    --------------- ξ-·₁
    L · M —→ L′ · M

    M —→ M′
    --------------- ξ-·₂
    V · M —→ V · M′

    ----------------------------- β-ƛ
    (ƛ x ⇒ N) · V —→ N [ x := V ]

The Agda version of the rules below will be similar, except that universal
quantifications are made explicit, and so are the predicates that indicate
which terms are values.

The rules break into two sorts. Compatibility rules direct us to
reduce some part of a term.  We give them names starting with the
Greek letter `ξ` (_xi_).  Once a term is sufficiently reduced, it will
consist of a constructor and a deconstructor, in our case `ƛ` and `·`,
which reduces directly.  We give them names starting with the Greek
letter `β` (_beta_) and such rules are traditionally called _beta rules_.

A bit of terminology: A term that matches the left-hand side of a
reduction rule is called a _redex_. In the redex `(ƛ x ⇒ N) · V`, we
may refer to `x` as the _formal parameter_ of the function, and `V`
as the _actual parameter_ of the function application.  Beta reduction
replaces the formal parameter by the actual parameter.

If a term is a value, then no reduction applies; conversely,
if a reduction applies to a term then it is not a value.
We will show in the next chapter that 
this exhausts the possibilities: every well-typed term
either reduces or is a value.

For numbers, zero does not reduce and successor reduces the subterm.
A case expression reduces its argument to a number, and then chooses
the zero or successor branch as appropriate.  A fixpoint replaces
the bound variable by the entire fixpoint term; this is the one
case where we substitute by a term that is not a value.

Here are the rules formalised in Agda:

{% raw %}<pre class="Agda"><a id="19600" class="Keyword">infix</a> <a id="19606" class="Number">4</a> <a id="19608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19619" class="Datatype Operator">_—→_</a>

<a id="19614" class="Keyword">data</a> <a id="_—→_"></a><a id="19619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19619" class="Datatype Operator">_—→_</a> <a id="19624" class="Symbol">:</a> <a id="19626" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="19631" class="Symbol">→</a> <a id="19633" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="19638" class="Symbol">→</a> <a id="19640" class="PrimitiveType">Set</a> <a id="19644" class="Keyword">where</a>

  <a id="_—→_.ξ-·₁"></a><a id="19653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19653" class="InductiveConstructor">ξ-·₁</a> <a id="19658" class="Symbol">:</a> <a id="19660" class="Symbol">∀</a> <a id="19662" class="Symbol">{</a><a id="19663" href="plfa.part2.Lambda.html#19663" class="Bound">L</a> <a id="19665" href="plfa.part2.Lambda.html#19665" class="Bound">L′</a> <a id="19668" href="plfa.part2.Lambda.html#19668" class="Bound">M</a><a id="19669" class="Symbol">}</a>
    <a id="19675" class="Symbol">→</a> <a id="19677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19663" class="Bound">L</a> <a id="19679" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="19682" href="plfa.part2.Lambda.html#19665" class="Bound">L′</a>
      <a id="19691" class="Comment">-----------------</a>
    <a id="19713" class="Symbol">→</a> <a id="19715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19663" class="Bound">L</a> <a id="19717" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="19719" href="plfa.part2.Lambda.html#19668" class="Bound">M</a> <a id="19721" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="19724" href="plfa.part2.Lambda.html#19665" class="Bound">L′</a> <a id="19727" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="19729" href="plfa.part2.Lambda.html#19668" class="Bound">M</a>

  <a id="_—→_.ξ-·₂"></a><a id="19734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19734" class="InductiveConstructor">ξ-·₂</a> <a id="19739" class="Symbol">:</a> <a id="19741" class="Symbol">∀</a> <a id="19743" class="Symbol">{</a><a id="19744" href="plfa.part2.Lambda.html#19744" class="Bound">V</a> <a id="19746" href="plfa.part2.Lambda.html#19746" class="Bound">M</a> <a id="19748" href="plfa.part2.Lambda.html#19748" class="Bound">M′</a><a id="19750" class="Symbol">}</a>
    <a id="19756" class="Symbol">→</a> <a id="19758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11595" class="Datatype">Value</a> <a id="19764" href="plfa.part2.Lambda.html#19744" class="Bound">V</a>
    <a id="19770" class="Symbol">→</a> <a id="19772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19746" class="Bound">M</a> <a id="19774" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="19777" href="plfa.part2.Lambda.html#19748" class="Bound">M′</a>
      <a id="19786" class="Comment">-----------------</a>
    <a id="19808" class="Symbol">→</a> <a id="19810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19744" class="Bound">V</a> <a id="19812" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="19814" href="plfa.part2.Lambda.html#19746" class="Bound">M</a> <a id="19816" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="19819" href="plfa.part2.Lambda.html#19744" class="Bound">V</a> <a id="19821" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="19823" href="plfa.part2.Lambda.html#19748" class="Bound">M′</a>

  <a id="_—→_.β-ƛ"></a><a id="19829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19829" class="InductiveConstructor">β-ƛ</a> <a id="19833" class="Symbol">:</a> <a id="19835" class="Symbol">∀</a> <a id="19837" class="Symbol">{</a><a id="19838" href="plfa.part2.Lambda.html#19838" class="Bound">x</a> <a id="19840" href="plfa.part2.Lambda.html#19840" class="Bound">N</a> <a id="19842" href="plfa.part2.Lambda.html#19842" class="Bound">V</a><a id="19843" class="Symbol">}</a>
    <a id="19849" class="Symbol">→</a> <a id="19851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11595" class="Datatype">Value</a> <a id="19857" href="plfa.part2.Lambda.html#19842" class="Bound">V</a>
      <a id="19865" class="Comment">------------------------------</a>
    <a id="19900" class="Symbol">→</a> <a id="19902" class="Symbol">(</a><a id="19903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="19905" href="plfa.part2.Lambda.html#19838" class="Bound">x</a> <a id="19907" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="19909" href="plfa.part2.Lambda.html#19840" class="Bound">N</a><a id="19910" class="Symbol">)</a> <a id="19912" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="19914" href="plfa.part2.Lambda.html#19842" class="Bound">V</a> <a id="19916" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="19919" href="plfa.part2.Lambda.html#19840" class="Bound">N</a> <a id="19921" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="19923" href="plfa.part2.Lambda.html#19838" class="Bound">x</a> <a id="19925" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="19928" href="plfa.part2.Lambda.html#19842" class="Bound">V</a> <a id="19930" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>

  <a id="_—→_.ξ-suc"></a><a id="19935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19935" class="InductiveConstructor">ξ-suc</a> <a id="19941" class="Symbol">:</a> <a id="19943" class="Symbol">∀</a> <a id="19945" class="Symbol">{</a><a id="19946" href="plfa.part2.Lambda.html#19946" class="Bound">M</a> <a id="19948" href="plfa.part2.Lambda.html#19948" class="Bound">M′</a><a id="19950" class="Symbol">}</a>
    <a id="19956" class="Symbol">→</a> <a id="19958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19946" class="Bound">M</a> <a id="19960" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="19963" href="plfa.part2.Lambda.html#19948" class="Bound">M′</a>
      <a id="19972" class="Comment">------------------</a>
    <a id="19995" class="Symbol">→</a> <a id="19997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="20002" href="plfa.part2.Lambda.html#19946" class="Bound">M</a> <a id="20004" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="20007" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="20012" href="plfa.part2.Lambda.html#19948" class="Bound">M′</a>

  <a id="_—→_.ξ-case"></a><a id="20018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20018" class="InductiveConstructor">ξ-case</a> <a id="20025" class="Symbol">:</a> <a id="20027" class="Symbol">∀</a> <a id="20029" class="Symbol">{</a><a id="20030" href="plfa.part2.Lambda.html#20030" class="Bound">x</a> <a id="20032" href="plfa.part2.Lambda.html#20032" class="Bound">L</a> <a id="20034" href="plfa.part2.Lambda.html#20034" class="Bound">L′</a> <a id="20037" href="plfa.part2.Lambda.html#20037" class="Bound">M</a> <a id="20039" href="plfa.part2.Lambda.html#20039" class="Bound">N</a><a id="20040" class="Symbol">}</a>
    <a id="20046" class="Symbol">→</a> <a id="20048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20032" class="Bound">L</a> <a id="20050" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="20053" href="plfa.part2.Lambda.html#20034" class="Bound">L′</a>
      <a id="20062" class="Comment">-----------------------------------------------------------------</a>
    <a id="20132" class="Symbol">→</a> <a id="20134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20139" href="plfa.part2.Lambda.html#20032" class="Bound">L</a> <a id="20141" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20148" href="plfa.part2.Lambda.html#20037" class="Bound">M</a> <a id="20150" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20155" href="plfa.part2.Lambda.html#20030" class="Bound">x</a> <a id="20157" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20159" href="plfa.part2.Lambda.html#20039" class="Bound">N</a> <a id="20161" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="20163" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="20166" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="20171" href="plfa.part2.Lambda.html#20034" class="Bound">L′</a> <a id="20174" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20181" href="plfa.part2.Lambda.html#20037" class="Bound">M</a> <a id="20183" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20188" href="plfa.part2.Lambda.html#20030" class="Bound">x</a> <a id="20190" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20192" href="plfa.part2.Lambda.html#20039" class="Bound">N</a> <a id="20194" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>

  <a id="_—→_.β-zero"></a><a id="20199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20199" class="InductiveConstructor">β-zero</a> <a id="20206" class="Symbol">:</a> <a id="20208" class="Symbol">∀</a> <a id="20210" class="Symbol">{</a><a id="20211" href="plfa.part2.Lambda.html#20211" class="Bound">x</a> <a id="20213" href="plfa.part2.Lambda.html#20213" class="Bound">M</a> <a id="20215" href="plfa.part2.Lambda.html#20215" class="Bound">N</a><a id="20216" class="Symbol">}</a>
      <a id="20224" class="Comment">----------------------------------------</a>
    <a id="20269" class="Symbol">→</a> <a id="20271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20276" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="20282" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20289" href="plfa.part2.Lambda.html#20213" class="Bound">M</a> <a id="20291" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20296" href="plfa.part2.Lambda.html#20211" class="Bound">x</a> <a id="20298" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20300" href="plfa.part2.Lambda.html#20215" class="Bound">N</a> <a id="20302" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="20304" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="20307" href="plfa.part2.Lambda.html#20213" class="Bound">M</a>

  <a id="_—→_.β-suc"></a><a id="20312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20312" class="InductiveConstructor">β-suc</a> <a id="20318" class="Symbol">:</a> <a id="20320" class="Symbol">∀</a> <a id="20322" class="Symbol">{</a><a id="20323" href="plfa.part2.Lambda.html#20323" class="Bound">x</a> <a id="20325" href="plfa.part2.Lambda.html#20325" class="Bound">V</a> <a id="20327" href="plfa.part2.Lambda.html#20327" class="Bound">M</a> <a id="20329" href="plfa.part2.Lambda.html#20329" class="Bound">N</a><a id="20330" class="Symbol">}</a>
    <a id="20336" class="Symbol">→</a> <a id="20338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11595" class="Datatype">Value</a> <a id="20344" href="plfa.part2.Lambda.html#20325" class="Bound">V</a>
      <a id="20352" class="Comment">---------------------------------------------------</a>
    <a id="20408" class="Symbol">→</a> <a id="20410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20415" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="20420" href="plfa.part2.Lambda.html#20325" class="Bound">V</a> <a id="20422" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20429" href="plfa.part2.Lambda.html#20327" class="Bound">M</a> <a id="20431" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20436" href="plfa.part2.Lambda.html#20323" class="Bound">x</a> <a id="20438" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20440" href="plfa.part2.Lambda.html#20329" class="Bound">N</a> <a id="20442" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="20444" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="20447" href="plfa.part2.Lambda.html#20329" class="Bound">N</a> <a id="20449" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="20451" href="plfa.part2.Lambda.html#20323" class="Bound">x</a> <a id="20453" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="20456" href="plfa.part2.Lambda.html#20325" class="Bound">V</a> <a id="20458" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>

  <a id="_—→_.β-μ"></a><a id="20463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20463" class="InductiveConstructor">β-μ</a> <a id="20467" class="Symbol">:</a> <a id="20469" class="Symbol">∀</a> <a id="20471" class="Symbol">{</a><a id="20472" href="plfa.part2.Lambda.html#20472" class="Bound">x</a> <a id="20474" href="plfa.part2.Lambda.html#20474" class="Bound">M</a><a id="20475" class="Symbol">}</a>
      <a id="20483" class="Comment">------------------------------</a>
    <a id="20518" class="Symbol">→</a> <a id="20520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="20522" href="plfa.part2.Lambda.html#20472" class="Bound">x</a> <a id="20524" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="20526" href="plfa.part2.Lambda.html#20474" class="Bound">M</a> <a id="20528" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="20531" href="plfa.part2.Lambda.html#20474" class="Bound">M</a> <a id="20533" href="plfa.part2.Lambda.html#14978" class="Function Operator">[</a> <a id="20535" href="plfa.part2.Lambda.html#20472" class="Bound">x</a> <a id="20537" href="plfa.part2.Lambda.html#14978" class="Function Operator">:=</a> <a id="20540" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="20542" href="plfa.part2.Lambda.html#20472" class="Bound">x</a> <a id="20544" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="20546" href="plfa.part2.Lambda.html#20474" class="Bound">M</a> <a id="20548" href="plfa.part2.Lambda.html#14978" class="Function Operator">]</a>
</pre>{% endraw %}
The reduction rules are carefully designed to ensure that subterms
of a term are reduced to values before the whole term is reduced.
This is referred to as _call-by-value_ reduction.

Further, we have arranged that subterms are reduced in a
left-to-right order.  This means that reduction is _deterministic_:
for any term, there is at most one other term to which it reduces.
Put another way, our reduction relation `—→` is in fact a function.

This style of explaining the meaning of terms is called
a _small-step operational semantics_.  If `M —→ N`, we say that
term `M` _reduces_ to term `N`, or equivalently,
term `M` _steps_ to term `N`.  Each compatibility rule has
another reduction rule in its premise; so a step always consists
of a beta rule, possibly adjusted by zero or more compatibility rules.


#### Quiz

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?  (Where `twoᶜ` and `sucᶜ` are as
defined above.)

    twoᶜ · sucᶜ · `zero  —→  ???

1.  `` sucᶜ · (sucᶜ · `zero) ``
2.  `` (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero ``
3.  `` `zero ``


## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `—↠` of the step relation `—→`.

We define reflexive and transitive closure as a sequence of zero or
more steps of the underlying relation, along lines similar to that for
reasoning about chains of equalities in
Chapter [Equality]({{ site.baseurl }}/Equality/):
{% raw %}<pre class="Agda"><a id="22544" class="Keyword">infix</a>  <a id="22551" class="Number">2</a> <a id="22553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22609" class="Datatype Operator">_—↠_</a>
<a id="22558" class="Keyword">infix</a>  <a id="22565" class="Number">1</a> <a id="22567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22759" class="Function Operator">begin_</a>
<a id="22574" class="Keyword">infixr</a> <a id="22581" class="Number">2</a> <a id="22583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">_—→⟨_⟩_</a>
<a id="22591" class="Keyword">infix</a>  <a id="22598" class="Number">3</a> <a id="22600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22642" class="InductiveConstructor Operator">_∎</a>

<a id="22604" class="Keyword">data</a> <a id="_—↠_"></a><a id="22609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22609" class="Datatype Operator">_—↠_</a> <a id="22614" class="Symbol">:</a> <a id="22616" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="22621" class="Symbol">→</a> <a id="22623" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="22628" class="Symbol">→</a> <a id="22630" class="PrimitiveType">Set</a> <a id="22634" class="Keyword">where</a>
  <a id="_—↠_._∎"></a><a id="22642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22642" class="InductiveConstructor Operator">_∎</a> <a id="22645" class="Symbol">:</a> <a id="22647" class="Symbol">∀</a> <a id="22649" href="plfa.part2.Lambda.html#22649" class="Bound">M</a>
      <a id="22657" class="Comment">---------</a>
    <a id="22671" class="Symbol">→</a> <a id="22673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22649" class="Bound">M</a> <a id="22675" href="plfa.part2.Lambda.html#22609" class="Datatype Operator">—↠</a> <a id="22678" href="plfa.part2.Lambda.html#22649" class="Bound">M</a>

  <a id="_—↠_._—→⟨_⟩_"></a><a id="22683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">_—→⟨_⟩_</a> <a id="22691" class="Symbol">:</a> <a id="22693" class="Symbol">∀</a> <a id="22695" href="plfa.part2.Lambda.html#22695" class="Bound">L</a> <a id="22697" class="Symbol">{</a><a id="22698" href="plfa.part2.Lambda.html#22698" class="Bound">M</a> <a id="22700" href="plfa.part2.Lambda.html#22700" class="Bound">N</a><a id="22701" class="Symbol">}</a>
    <a id="22707" class="Symbol">→</a> <a id="22709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22695" class="Bound">L</a> <a id="22711" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="22714" href="plfa.part2.Lambda.html#22698" class="Bound">M</a>
    <a id="22720" class="Symbol">→</a> <a id="22722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22698" class="Bound">M</a> <a id="22724" href="plfa.part2.Lambda.html#22609" class="Datatype Operator">—↠</a> <a id="22727" href="plfa.part2.Lambda.html#22700" class="Bound">N</a>
      <a id="22735" class="Comment">---------</a>
    <a id="22749" class="Symbol">→</a> <a id="22751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22695" class="Bound">L</a> <a id="22753" href="plfa.part2.Lambda.html#22609" class="Datatype Operator">—↠</a> <a id="22756" href="plfa.part2.Lambda.html#22700" class="Bound">N</a>

<a id="begin_"></a><a id="22759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22759" class="Function Operator">begin_</a> <a id="22766" class="Symbol">:</a> <a id="22768" class="Symbol">∀</a> <a id="22770" class="Symbol">{</a><a id="22771" href="plfa.part2.Lambda.html#22771" class="Bound">M</a> <a id="22773" href="plfa.part2.Lambda.html#22773" class="Bound">N</a><a id="22774" class="Symbol">}</a>
  <a id="22778" class="Symbol">→</a> <a id="22780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22771" class="Bound">M</a> <a id="22782" href="plfa.part2.Lambda.html#22609" class="Datatype Operator">—↠</a> <a id="22785" href="plfa.part2.Lambda.html#22773" class="Bound">N</a>
    <a id="22791" class="Comment">------</a>
  <a id="22800" class="Symbol">→</a> <a id="22802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22771" class="Bound">M</a> <a id="22804" href="plfa.part2.Lambda.html#22609" class="Datatype Operator">—↠</a> <a id="22807" href="plfa.part2.Lambda.html#22773" class="Bound">N</a>
<a id="22809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22759" class="Function Operator">begin</a> <a id="22815" href="plfa.part2.Lambda.html#22815" class="Bound">M—↠N</a> <a id="22820" class="Symbol">=</a> <a id="22822" href="plfa.part2.Lambda.html#22815" class="Bound">M—↠N</a>
</pre>{% endraw %}We can read this as follows:

* From term `M`, we can take no steps, giving a step of type `M —↠ M`.
  It is written `M ∎`.

* From term `L` we can take a single step of type `L —→ M` followed by zero
  or more steps of type `M —↠ N`, giving a step of type `L —↠ N`. It is
  written `L —→⟨ L—→M ⟩ M—↠N`, where `L—→M` and `M—↠N` are steps of the
  appropriate type.

The notation is chosen to allow us to lay out example reductions in an
appealing way, as we will see in the next section.

An alternative is to define reflexive and transitive closure directly,
as the smallest relation that includes `—→` and is also reflexive
and transitive.  We could do so as follows:
{% raw %}<pre class="Agda"><a id="23505" class="Keyword">data</a> <a id="_—↠′_"></a><a id="23510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23510" class="Datatype Operator">_—↠′_</a> <a id="23516" class="Symbol">:</a> <a id="23518" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="23523" class="Symbol">→</a> <a id="23525" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="23530" class="Symbol">→</a> <a id="23532" class="PrimitiveType">Set</a> <a id="23536" class="Keyword">where</a>

  <a id="_—↠′_.step′"></a><a id="23545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23545" class="InductiveConstructor">step′</a> <a id="23551" class="Symbol">:</a> <a id="23553" class="Symbol">∀</a> <a id="23555" class="Symbol">{</a><a id="23556" href="plfa.part2.Lambda.html#23556" class="Bound">M</a> <a id="23558" href="plfa.part2.Lambda.html#23558" class="Bound">N</a><a id="23559" class="Symbol">}</a>
    <a id="23565" class="Symbol">→</a> <a id="23567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23556" class="Bound">M</a> <a id="23569" href="plfa.part2.Lambda.html#19619" class="Datatype Operator">—→</a> <a id="23572" href="plfa.part2.Lambda.html#23558" class="Bound">N</a>
      <a id="23580" class="Comment">-------</a>
    <a id="23592" class="Symbol">→</a> <a id="23594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23556" class="Bound">M</a> <a id="23596" href="plfa.part2.Lambda.html#23510" class="Datatype Operator">—↠′</a> <a id="23600" href="plfa.part2.Lambda.html#23558" class="Bound">N</a>

  <a id="_—↠′_.refl′"></a><a id="23605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23605" class="InductiveConstructor">refl′</a> <a id="23611" class="Symbol">:</a> <a id="23613" class="Symbol">∀</a> <a id="23615" class="Symbol">{</a><a id="23616" href="plfa.part2.Lambda.html#23616" class="Bound">M</a><a id="23617" class="Symbol">}</a>
      <a id="23625" class="Comment">-------</a>
    <a id="23637" class="Symbol">→</a> <a id="23639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23616" class="Bound">M</a> <a id="23641" href="plfa.part2.Lambda.html#23510" class="Datatype Operator">—↠′</a> <a id="23645" href="plfa.part2.Lambda.html#23616" class="Bound">M</a>

  <a id="_—↠′_.trans′"></a><a id="23650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23650" class="InductiveConstructor">trans′</a> <a id="23657" class="Symbol">:</a> <a id="23659" class="Symbol">∀</a> <a id="23661" class="Symbol">{</a><a id="23662" href="plfa.part2.Lambda.html#23662" class="Bound">L</a> <a id="23664" href="plfa.part2.Lambda.html#23664" class="Bound">M</a> <a id="23666" href="plfa.part2.Lambda.html#23666" class="Bound">N</a><a id="23667" class="Symbol">}</a>
    <a id="23673" class="Symbol">→</a> <a id="23675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23662" class="Bound">L</a> <a id="23677" href="plfa.part2.Lambda.html#23510" class="Datatype Operator">—↠′</a> <a id="23681" href="plfa.part2.Lambda.html#23664" class="Bound">M</a>
    <a id="23687" class="Symbol">→</a> <a id="23689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23664" class="Bound">M</a> <a id="23691" href="plfa.part2.Lambda.html#23510" class="Datatype Operator">—↠′</a> <a id="23695" href="plfa.part2.Lambda.html#23666" class="Bound">N</a>
      <a id="23703" class="Comment">-------</a>
    <a id="23715" class="Symbol">→</a> <a id="23717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23662" class="Bound">L</a> <a id="23719" href="plfa.part2.Lambda.html#23510" class="Datatype Operator">—↠′</a> <a id="23723" href="plfa.part2.Lambda.html#23666" class="Bound">N</a>
</pre>{% endraw %}The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

{% raw %}<pre class="Agda"><a id="24099" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Confluence

One important property a reduction relation might satisfy is
to be _confluent_.  If term `L` reduces to two other terms,
`M` and `N`, then both of these reduce to a common term `P`.
It can be illustrated as follows:

               L
              / \
             /   \
            /     \
           M       N
            \     /
             \   /
              \ /
               P

Here `L`, `M`, `N` are universally quantified while `P`
is existentially quantified.  If each line stands for zero
or more reduction steps, this is called confluence,
while if the top two lines stand for a single reduction
step and the bottom two stand for zero or more reduction
steps it is called the diamond property. In symbols:

    confluence : ∀ {L M N} → ∃[ P ]
      ( ((L —↠ M) × (L —↠ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

    diamond : ∀ {L M N} → ∃[ P ]
      ( ((L —→ M) × (L —→ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

The reduction system studied in this chapter is deterministic.
In symbols:

    deterministic : ∀ {L M N}
      → L —→ M
      → L —→ N
        ------
      → M ≡ N

It is easy to show that every deterministic relation satisfies
the diamond property, and that every relation that satisfies
the diamond property is confluent.  Hence, all the reduction
systems studied in this text are trivially confluent.


## Examples

We start with a simple example. The Church numeral two applied to the
successor function and zero yields the natural number two:
{% raw %}<pre class="Agda"><a id="25669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#25669" class="Function">_</a> <a id="25671" class="Symbol">:</a> <a id="25673" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="25678" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25680" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="25685" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25687" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="25693" href="plfa.part2.Lambda.html#22609" class="Datatype Operator">—↠</a> <a id="25696" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="25701" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="25706" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="25712" class="Symbol">_</a> <a id="25714" class="Symbol">=</a>
  <a id="25718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22759" class="Function Operator">begin</a>
    <a id="25728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="25733" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25735" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="25740" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25742" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="25750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="25754" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="25759" class="Symbol">(</a><a id="25760" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="25764" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a><a id="25767" class="Symbol">)</a> <a id="25769" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="25775" class="Symbol">(</a><a id="25776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="25778" class="String">&quot;z&quot;</a> <a id="25782" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="25784" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="25789" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25791" class="Symbol">(</a><a id="25792" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="25797" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25799" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="25801" class="String">&quot;z&quot;</a><a id="25804" class="Symbol">))</a> <a id="25807" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25809" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="25817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="25821" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="25825" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a> <a id="25832" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="25838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="25843" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25845" class="Symbol">(</a><a id="25846" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="25851" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25853" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="25858" class="Symbol">)</a>
  <a id="25862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="25866" href="plfa.part2.Lambda.html#19734" class="InductiveConstructor">ξ-·₂</a> <a id="25871" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a> <a id="25875" class="Symbol">(</a><a id="25876" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="25880" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="25886" class="Symbol">)</a> <a id="25888" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="25894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="25899" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="25901" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="25906" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="25914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="25918" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="25922" class="Symbol">(</a><a id="25923" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="25929" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="25935" class="Symbol">)</a> <a id="25937" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="25943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="25948" class="Symbol">(</a><a id="25949" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="25954" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="25959" class="Symbol">)</a>
  <a id="25963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22642" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
Here is a sample reduction demonstrating that two plus two is four:
{% raw %}<pre class="Agda"><a id="26042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26042" class="Function">_</a> <a id="26044" class="Symbol">:</a> <a id="26046" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26051" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26053" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26057" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26059" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26063" href="plfa.part2.Lambda.html#22609" class="Datatype Operator">—↠</a> <a id="26066" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26071" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26076" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26081" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26086" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="26092" class="Symbol">_</a> <a id="26094" class="Symbol">=</a>
  <a id="26098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22759" class="Function Operator">begin</a>
    <a id="26108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4558" class="Function">plus</a> <a id="26113" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26115" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26119" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26121" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="26131" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="26136" class="Symbol">(</a><a id="26137" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="26142" href="plfa.part2.Lambda.html#20463" class="InductiveConstructor">β-μ</a><a id="26145" class="Symbol">)</a> <a id="26147" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="26153" class="Symbol">(</a><a id="26154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26156" class="String">&quot;m&quot;</a> <a id="26160" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="26162" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26164" class="String">&quot;n&quot;</a> <a id="26168" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26181" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26183" class="String">&quot;m&quot;</a> <a id="26187" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26194" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26196" class="String">&quot;n&quot;</a> <a id="26200" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26205" class="String">&quot;m&quot;</a> <a id="26209" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26211" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26216" class="Symbol">(</a><a id="26217" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26222" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26224" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26226" class="String">&quot;m&quot;</a> <a id="26230" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26232" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26234" class="String">&quot;n&quot;</a><a id="26237" class="Symbol">)</a> <a id="26239" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26240" class="Symbol">)</a>
        <a id="26250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26252" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26256" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26258" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="26268" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="26273" class="Symbol">(</a><a id="26274" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="26278" class="Symbol">(</a><a id="26279" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="26285" class="Symbol">(</a><a id="26286" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="26292" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="26298" class="Symbol">)))</a> <a id="26302" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="26308" class="Symbol">(</a><a id="26309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26311" class="String">&quot;n&quot;</a> <a id="26315" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26328" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26332" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26339" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26341" class="String">&quot;n&quot;</a> <a id="26345" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26350" class="String">&quot;m&quot;</a> <a id="26354" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26356" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26361" class="Symbol">(</a><a id="26362" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26367" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26369" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26371" class="String">&quot;m&quot;</a> <a id="26375" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26377" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26379" class="String">&quot;n&quot;</a><a id="26382" class="Symbol">)</a> <a id="26384" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26385" class="Symbol">)</a>
         <a id="26396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26398" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="26408" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="26412" class="Symbol">(</a><a id="26413" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="26419" class="Symbol">(</a><a id="26420" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="26426" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="26432" class="Symbol">))</a> <a id="26435" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="26441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26446" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26450" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26457" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26461" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26466" class="String">&quot;m&quot;</a> <a id="26470" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26472" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26477" class="Symbol">(</a><a id="26478" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26483" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26485" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26487" class="String">&quot;m&quot;</a> <a id="26491" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26493" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="26496" class="Symbol">)</a> <a id="26498" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
  <a id="26502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="26506" href="plfa.part2.Lambda.html#20312" class="InductiveConstructor">β-suc</a> <a id="26512" class="Symbol">(</a><a id="26513" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="26519" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="26525" class="Symbol">)</a> <a id="26527" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="26533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="26538" class="Symbol">(</a><a id="26539" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26544" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26546" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26551" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="26557" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26559" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="26562" class="Symbol">)</a>
  <a id="26566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="26570" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="26576" class="Symbol">(</a><a id="26577" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="26582" class="Symbol">(</a><a id="26583" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="26588" href="plfa.part2.Lambda.html#20463" class="InductiveConstructor">β-μ</a><a id="26591" class="Symbol">))</a> <a id="26594" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="26600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="26605" class="Symbol">((</a><a id="26607" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26609" class="String">&quot;m&quot;</a> <a id="26613" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="26615" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26617" class="String">&quot;n&quot;</a> <a id="26621" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26634" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26636" class="String">&quot;m&quot;</a> <a id="26640" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26647" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26649" class="String">&quot;n&quot;</a> <a id="26653" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26658" class="String">&quot;m&quot;</a> <a id="26662" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26664" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26669" class="Symbol">(</a><a id="26670" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26675" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26677" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26679" class="String">&quot;m&quot;</a> <a id="26683" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26685" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26687" class="String">&quot;n&quot;</a><a id="26690" class="Symbol">)</a> <a id="26692" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26693" class="Symbol">)</a>
        <a id="26703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26705" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26710" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="26716" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26718" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="26721" class="Symbol">)</a>
  <a id="26725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="26729" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="26735" class="Symbol">(</a><a id="26736" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="26741" class="Symbol">(</a><a id="26742" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="26746" class="Symbol">(</a><a id="26747" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="26753" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="26759" class="Symbol">)))</a> <a id="26763" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="26769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="26774" class="Symbol">((</a><a id="26776" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26778" class="String">&quot;n&quot;</a> <a id="26782" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26795" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26800" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="26806" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26813" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26815" class="String">&quot;n&quot;</a> <a id="26819" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26824" class="String">&quot;m&quot;</a> <a id="26828" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26830" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26835" class="Symbol">(</a><a id="26836" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26841" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26843" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26845" class="String">&quot;m&quot;</a> <a id="26849" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26851" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26853" class="String">&quot;n&quot;</a><a id="26856" class="Symbol">)</a> <a id="26858" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26859" class="Symbol">)</a>
        <a id="26869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26871" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="26874" class="Symbol">)</a>
  <a id="26878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="26882" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="26888" class="Symbol">(</a><a id="26889" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="26893" class="Symbol">(</a><a id="26894" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="26900" class="Symbol">(</a><a id="26901" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="26907" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="26913" class="Symbol">)))</a> <a id="26917" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="26923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="26928" class="Symbol">(</a><a id="26929" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="26934" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26939" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="26945" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26952" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26956" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26961" class="String">&quot;m&quot;</a> <a id="26965" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26967" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26972" class="Symbol">(</a><a id="26973" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26978" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26980" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26982" class="String">&quot;m&quot;</a> <a id="26986" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26988" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="26991" class="Symbol">)</a> <a id="26993" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26994" class="Symbol">)</a>
  <a id="26998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="27002" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="27008" class="Symbol">(</a><a id="27009" href="plfa.part2.Lambda.html#20312" class="InductiveConstructor">β-suc</a> <a id="27015" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="27021" class="Symbol">)</a> <a id="27023" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="27029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27034" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27039" class="Symbol">(</a><a id="27040" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27045" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27047" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27053" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27055" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27058" class="Symbol">)</a>
  <a id="27062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="27066" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="27072" class="Symbol">(</a><a id="27073" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="27079" class="Symbol">(</a><a id="27080" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="27085" class="Symbol">(</a><a id="27086" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="27091" href="plfa.part2.Lambda.html#20463" class="InductiveConstructor">β-μ</a><a id="27094" class="Symbol">)))</a> <a id="27098" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="27104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27109" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27114" class="Symbol">((</a><a id="27116" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27118" class="String">&quot;m&quot;</a> <a id="27122" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27124" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27126" class="String">&quot;n&quot;</a> <a id="27130" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27143" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27145" class="String">&quot;m&quot;</a> <a id="27149" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27156" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27158" class="String">&quot;n&quot;</a> <a id="27162" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27167" class="String">&quot;m&quot;</a> <a id="27171" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27173" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27178" class="Symbol">(</a><a id="27179" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27184" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27186" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27188" class="String">&quot;m&quot;</a> <a id="27192" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27194" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27196" class="String">&quot;n&quot;</a><a id="27199" class="Symbol">)</a> <a id="27201" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27202" class="Symbol">)</a>
        <a id="27212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27214" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27220" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27222" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27225" class="Symbol">)</a>
  <a id="27229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="27233" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="27239" class="Symbol">(</a><a id="27240" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="27246" class="Symbol">(</a><a id="27247" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="27252" class="Symbol">(</a><a id="27253" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="27257" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="27263" class="Symbol">)))</a> <a id="27267" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="27273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27278" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27283" class="Symbol">((</a><a id="27285" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27287" class="String">&quot;n&quot;</a> <a id="27291" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27304" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27310" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27317" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27319" class="String">&quot;n&quot;</a> <a id="27323" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27328" class="String">&quot;m&quot;</a> <a id="27332" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27334" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27339" class="Symbol">(</a><a id="27340" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27345" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27347" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27349" class="String">&quot;m&quot;</a> <a id="27353" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27355" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27357" class="String">&quot;n&quot;</a><a id="27360" class="Symbol">)</a> <a id="27362" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27363" class="Symbol">)</a>
        <a id="27373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27375" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27378" class="Symbol">)</a>
  <a id="27382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="27386" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="27392" class="Symbol">(</a><a id="27393" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="27399" class="Symbol">(</a><a id="27400" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="27404" class="Symbol">(</a><a id="27405" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="27411" class="Symbol">(</a><a id="27412" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="27418" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="27424" class="Symbol">))))</a> <a id="27429" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="27435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27440" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27445" class="Symbol">(</a><a id="27446" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="27451" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27457" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27464" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27468" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27473" class="String">&quot;m&quot;</a> <a id="27477" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27479" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27484" class="Symbol">(</a><a id="27485" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27490" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27492" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27494" class="String">&quot;m&quot;</a> <a id="27498" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27500" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27503" class="Symbol">)</a> <a id="27505" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27506" class="Symbol">)</a>
  <a id="27510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="27514" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="27520" class="Symbol">(</a><a id="27521" href="plfa.part2.Lambda.html#19935" class="InductiveConstructor">ξ-suc</a> <a id="27527" href="plfa.part2.Lambda.html#20199" class="InductiveConstructor">β-zero</a><a id="27533" class="Symbol">)</a> <a id="27535" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="27541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27546" class="Symbol">(</a><a id="27547" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27552" class="Symbol">(</a><a id="27553" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27558" class="Symbol">(</a><a id="27559" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27564" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="27569" class="Symbol">)))</a>
  <a id="27575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22642" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
And here is a similar sample reduction for Church numerals:
{% raw %}<pre class="Agda"><a id="27646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#27646" class="Function">_</a> <a id="27648" class="Symbol">:</a> <a id="27650" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="27656" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27658" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="27663" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27665" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="27670" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27672" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="27677" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27679" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27685" href="plfa.part2.Lambda.html#22609" class="Datatype Operator">—↠</a> <a id="27688" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27693" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27698" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27703" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27708" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="27714" class="Symbol">_</a> <a id="27716" class="Symbol">=</a>
  <a id="27720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22759" class="Function Operator">begin</a>
    <a id="27730" class="Symbol">(</a><a id="27731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27733" class="String">&quot;m&quot;</a> <a id="27737" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27739" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27741" class="String">&quot;n&quot;</a> <a id="27745" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27747" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27749" class="String">&quot;s&quot;</a> <a id="27753" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27755" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27757" class="String">&quot;z&quot;</a> <a id="27761" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27763" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27765" class="String">&quot;m&quot;</a> <a id="27769" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27771" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27773" class="String">&quot;s&quot;</a> <a id="27777" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27779" class="Symbol">(</a><a id="27780" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27782" class="String">&quot;n&quot;</a> <a id="27786" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27788" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27790" class="String">&quot;s&quot;</a> <a id="27794" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27796" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27798" class="String">&quot;z&quot;</a><a id="27801" class="Symbol">))</a>
      <a id="27810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27812" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="27817" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27819" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="27824" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27826" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="27831" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27833" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="27841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="27845" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="27850" class="Symbol">(</a><a id="27851" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="27856" class="Symbol">(</a><a id="27857" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="27862" class="Symbol">(</a><a id="27863" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="27867" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a><a id="27870" class="Symbol">)))</a> <a id="27874" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="27880" class="Symbol">(</a><a id="27881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27883" class="String">&quot;n&quot;</a> <a id="27887" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27889" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27891" class="String">&quot;s&quot;</a> <a id="27895" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27897" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27899" class="String">&quot;z&quot;</a> <a id="27903" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27905" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="27910" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27912" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27914" class="String">&quot;s&quot;</a> <a id="27918" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27920" class="Symbol">(</a><a id="27921" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27923" class="String">&quot;n&quot;</a> <a id="27927" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27929" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27931" class="String">&quot;s&quot;</a> <a id="27935" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27937" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27939" class="String">&quot;z&quot;</a><a id="27942" class="Symbol">))</a>
      <a id="27951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27953" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="27958" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27960" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="27965" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27967" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="27975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="27979" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="27984" class="Symbol">(</a><a id="27985" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="27990" class="Symbol">(</a><a id="27991" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="27995" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a><a id="27998" class="Symbol">))</a> <a id="28001" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28007" class="Symbol">(</a><a id="28008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28010" class="String">&quot;s&quot;</a> <a id="28014" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28016" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28018" class="String">&quot;z&quot;</a> <a id="28022" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28024" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28029" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28031" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28033" class="String">&quot;s&quot;</a> <a id="28037" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28039" class="Symbol">(</a><a id="28040" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28045" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28047" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28049" class="String">&quot;s&quot;</a> <a id="28053" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28055" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28057" class="String">&quot;z&quot;</a><a id="28060" class="Symbol">))</a> <a id="28063" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28065" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28070" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28072" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28084" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="28089" class="Symbol">(</a><a id="28090" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28094" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a><a id="28097" class="Symbol">)</a> <a id="28099" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28105" class="Symbol">(</a><a id="28106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28108" class="String">&quot;z&quot;</a> <a id="28112" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28114" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28119" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28121" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28126" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28128" class="Symbol">(</a><a id="28129" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28134" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28136" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28141" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28143" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28145" class="String">&quot;z&quot;</a><a id="28148" class="Symbol">))</a> <a id="28151" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28153" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28165" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28169" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a> <a id="28176" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="28187" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28189" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28194" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28196" class="Symbol">(</a><a id="28197" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28202" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28204" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28209" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28211" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28216" class="Symbol">)</a>
  <a id="28220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28224" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="28229" class="Symbol">(</a><a id="28230" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28234" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a><a id="28237" class="Symbol">)</a> <a id="28239" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28245" class="Symbol">(</a><a id="28246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28248" class="String">&quot;z&quot;</a> <a id="28252" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28254" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28259" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28261" class="Symbol">(</a><a id="28262" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28267" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28269" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28271" class="String">&quot;z&quot;</a><a id="28274" class="Symbol">))</a> <a id="28277" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28279" class="Symbol">(</a><a id="28280" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28285" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28287" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28292" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28294" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28299" class="Symbol">)</a>
  <a id="28303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28307" href="plfa.part2.Lambda.html#19734" class="InductiveConstructor">ξ-·₂</a> <a id="28312" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a> <a id="28316" class="Symbol">(</a><a id="28317" href="plfa.part2.Lambda.html#19653" class="InductiveConstructor">ξ-·₁</a> <a id="28322" class="Symbol">(</a><a id="28323" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28327" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a><a id="28330" class="Symbol">))</a> <a id="28333" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28339" class="Symbol">(</a><a id="28340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28342" class="String">&quot;z&quot;</a> <a id="28346" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28348" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28353" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28355" class="Symbol">(</a><a id="28356" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28361" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28363" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28365" class="String">&quot;z&quot;</a><a id="28368" class="Symbol">))</a> <a id="28371" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28373" class="Symbol">((</a><a id="28375" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28377" class="String">&quot;z&quot;</a> <a id="28381" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28383" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28388" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28390" class="Symbol">(</a><a id="28391" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28396" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28398" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28400" class="String">&quot;z&quot;</a><a id="28403" class="Symbol">))</a> <a id="28406" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28408" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28413" class="Symbol">)</a>
  <a id="28417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28421" href="plfa.part2.Lambda.html#19734" class="InductiveConstructor">ξ-·₂</a> <a id="28426" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a> <a id="28430" class="Symbol">(</a><a id="28431" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28435" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="28441" class="Symbol">)</a> <a id="28443" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28449" class="Symbol">(</a><a id="28450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28452" class="String">&quot;z&quot;</a> <a id="28456" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28458" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28463" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28465" class="Symbol">(</a><a id="28466" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28471" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28473" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28475" class="String">&quot;z&quot;</a><a id="28478" class="Symbol">))</a> <a id="28481" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28483" class="Symbol">(</a><a id="28484" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28489" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28491" class="Symbol">(</a><a id="28492" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28497" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28499" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28504" class="Symbol">))</a>
  <a id="28509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28513" href="plfa.part2.Lambda.html#19734" class="InductiveConstructor">ξ-·₂</a> <a id="28518" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a> <a id="28522" class="Symbol">(</a><a id="28523" href="plfa.part2.Lambda.html#19734" class="InductiveConstructor">ξ-·₂</a> <a id="28528" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a> <a id="28532" class="Symbol">(</a><a id="28533" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28537" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="28543" class="Symbol">))</a> <a id="28546" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28552" class="Symbol">(</a><a id="28553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28555" class="String">&quot;z&quot;</a> <a id="28559" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28561" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28566" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28568" class="Symbol">(</a><a id="28569" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28574" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28576" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28578" class="String">&quot;z&quot;</a><a id="28581" class="Symbol">))</a> <a id="28584" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28586" class="Symbol">(</a><a id="28587" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28592" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28594" class="Symbol">(</a><a id="28595" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28600" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28605" class="Symbol">))</a>
  <a id="28610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28614" href="plfa.part2.Lambda.html#19734" class="InductiveConstructor">ξ-·₂</a> <a id="28619" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a> <a id="28623" class="Symbol">(</a><a id="28624" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28628" class="Symbol">(</a><a id="28629" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="28635" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="28641" class="Symbol">))</a> <a id="28644" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28650" class="Symbol">(</a><a id="28651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28653" class="String">&quot;z&quot;</a> <a id="28657" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28659" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28664" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28666" class="Symbol">(</a><a id="28667" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28672" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28674" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28676" class="String">&quot;z&quot;</a><a id="28679" class="Symbol">))</a> <a id="28682" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28684" class="Symbol">(</a><a id="28685" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28690" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28695" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28700" class="Symbol">)</a>
  <a id="28704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28708" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28712" class="Symbol">(</a><a id="28713" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="28719" class="Symbol">(</a><a id="28720" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="28726" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="28732" class="Symbol">))</a> <a id="28735" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="28746" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28748" class="Symbol">(</a><a id="28749" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28754" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28756" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28761" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28766" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28771" class="Symbol">)</a>
  <a id="28775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28779" href="plfa.part2.Lambda.html#19734" class="InductiveConstructor">ξ-·₂</a> <a id="28784" href="plfa.part2.Lambda.html#11623" class="InductiveConstructor">V-ƛ</a> <a id="28788" class="Symbol">(</a><a id="28789" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28793" class="Symbol">(</a><a id="28794" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="28800" class="Symbol">(</a><a id="28801" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="28807" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="28813" class="Symbol">)))</a> <a id="28817" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
    <a id="28823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="28828" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28830" class="Symbol">(</a><a id="28831" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28836" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28841" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28846" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28851" class="Symbol">)</a>
  <a id="28855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22683" class="InductiveConstructor Operator">—→⟨</a> <a id="28859" href="plfa.part2.Lambda.html#19829" class="InductiveConstructor">β-ƛ</a> <a id="28863" class="Symbol">(</a><a id="28864" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="28870" class="Symbol">(</a><a id="28871" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="28877" class="Symbol">(</a><a id="28878" href="plfa.part2.Lambda.html#11732" class="InductiveConstructor">V-suc</a> <a id="28884" href="plfa.part2.Lambda.html#11684" class="InductiveConstructor">V-zero</a><a id="28890" class="Symbol">)))</a> <a id="28894" href="plfa.part2.Lambda.html#22683" class="InductiveConstructor Operator">⟩</a>
   <a id="28899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="28904" class="Symbol">(</a><a id="28905" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28910" class="Symbol">(</a><a id="28911" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28916" class="Symbol">(</a><a id="28917" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28922" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28927" class="Symbol">)))</a>
  <a id="28933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22642" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

{% raw %}<pre class="Agda"><a id="29135" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

{% raw %}<pre class="Agda"><a id="29435" class="Keyword">infixr</a> <a id="29442" class="Number">7</a> <a id="29444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#29473" class="InductiveConstructor Operator">_⇒_</a>

<a id="29449" class="Keyword">data</a> <a id="Type"></a><a id="29454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#29454" class="Datatype">Type</a> <a id="29459" class="Symbol">:</a> <a id="29461" class="PrimitiveType">Set</a> <a id="29465" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="29473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#29473" class="InductiveConstructor Operator">_⇒_</a> <a id="29477" class="Symbol">:</a> <a id="29479" href="plfa.part2.Lambda.html#29454" class="Datatype">Type</a> <a id="29484" class="Symbol">→</a> <a id="29486" href="plfa.part2.Lambda.html#29454" class="Datatype">Type</a> <a id="29491" class="Symbol">→</a> <a id="29493" href="plfa.part2.Lambda.html#29454" class="Datatype">Type</a>
  <a id="Type.`ℕ"></a><a id="29500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#29500" class="InductiveConstructor">`ℕ</a> <a id="29503" class="Symbol">:</a> <a id="29505" href="plfa.part2.Lambda.html#29454" class="Datatype">Type</a>
</pre>{% endraw %}
### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus:

* ``(`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ`` stands for ``((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))``.
* `plus · two · two` stands for `(plus · two) · two`.

### Quiz

* What is the type of the following term?

    `` ƛ "s" ⇒ ` "s" · (` "s"  · `zero) ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    `` (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.


## Typing

### Contexts

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

A _context_ associates variables with types.  We let `Γ` and `Δ` range
over contexts.  We write `∅` for the empty context, and `Γ , x ⦂ A`
for the context that extends `Γ` by mapping variable `x` to type `A`.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ``

is the context that associates variable `` "s" `` with type `` `ℕ ⇒ `ℕ ``,
and variable `` "z" `` with type `` `ℕ ``.

Contexts are formalised as follows:

{% raw %}<pre class="Agda"><a id="31090" class="Keyword">infixl</a> <a id="31097" class="Number">5</a>  <a id="31100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31152" class="InductiveConstructor Operator">_,_⦂_</a>

<a id="31107" class="Keyword">data</a> <a id="Context"></a><a id="31112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31112" class="Datatype">Context</a> <a id="31120" class="Symbol">:</a> <a id="31122" class="PrimitiveType">Set</a> <a id="31126" class="Keyword">where</a>
  <a id="Context.∅"></a><a id="31134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31134" class="InductiveConstructor">∅</a>     <a id="31140" class="Symbol">:</a> <a id="31142" href="plfa.part2.Lambda.html#31112" class="Datatype">Context</a>
  <a id="Context._,_⦂_"></a><a id="31152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31152" class="InductiveConstructor Operator">_,_⦂_</a> <a id="31158" class="Symbol">:</a> <a id="31160" href="plfa.part2.Lambda.html#31112" class="Datatype">Context</a> <a id="31168" class="Symbol">→</a> <a id="31170" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="31173" class="Symbol">→</a> <a id="31175" href="plfa.part2.Lambda.html#29454" class="Datatype">Type</a> <a id="31180" class="Symbol">→</a> <a id="31182" href="plfa.part2.Lambda.html#31112" class="Datatype">Context</a>
</pre>{% endraw %}

#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

{% raw %}<pre class="Agda"><a id="31435" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
### Lookup judgment

We have two forms of _judgment_.  The first is written

    Γ ∋ x ⦂ A

and indicates in context `Γ` that variable `x` has type `A`.
It is called _lookup_.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

give us the types associated with variables `` "z" `` and `` "s" ``,
respectively.  The symbol `∋` (pronounced "ni", for "in"
backwards) is chosen because checking that `Γ ∋ x ⦂ A` is analogous to
checking whether `x ⦂ A` appears in a list corresponding to `Γ`.

If two variables in a context have the same name, then lookup
should return the most recently bound variable, which _shadows_
the other variables.  For example,

* `` ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ∋ "x" ⦂ `ℕ ``.

Here `` "x" ⦂ `ℕ ⇒ `ℕ `` is shadowed by `` "x" ⦂ `ℕ ``.

Lookup is formalised as follows:
{% raw %}<pre class="Agda"><a id="32324" class="Keyword">infix</a>  <a id="32331" class="Number">4</a>  <a id="32334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32346" class="Datatype Operator">_∋_⦂_</a>

<a id="32341" class="Keyword">data</a> <a id="_∋_⦂_"></a><a id="32346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32346" class="Datatype Operator">_∋_⦂_</a> <a id="32352" class="Symbol">:</a> <a id="32354" href="plfa.part2.Lambda.html#31112" class="Datatype">Context</a> <a id="32362" class="Symbol">→</a> <a id="32364" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="32367" class="Symbol">→</a> <a id="32369" href="plfa.part2.Lambda.html#29454" class="Datatype">Type</a> <a id="32374" class="Symbol">→</a> <a id="32376" class="PrimitiveType">Set</a> <a id="32380" class="Keyword">where</a>

  <a id="_∋_⦂_.Z"></a><a id="32389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32389" class="InductiveConstructor">Z</a> <a id="32391" class="Symbol">:</a> <a id="32393" class="Symbol">∀</a> <a id="32395" class="Symbol">{</a><a id="32396" href="plfa.part2.Lambda.html#32396" class="Bound">Γ</a> <a id="32398" href="plfa.part2.Lambda.html#32398" class="Bound">x</a> <a id="32400" href="plfa.part2.Lambda.html#32400" class="Bound">A</a><a id="32401" class="Symbol">}</a>
      <a id="32409" class="Comment">------------------</a>
    <a id="32432" class="Symbol">→</a> <a id="32434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32396" class="Bound">Γ</a> <a id="32436" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">,</a> <a id="32438" href="plfa.part2.Lambda.html#32398" class="Bound">x</a> <a id="32440" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">⦂</a> <a id="32442" href="plfa.part2.Lambda.html#32400" class="Bound">A</a> <a id="32444" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">∋</a> <a id="32446" href="plfa.part2.Lambda.html#32398" class="Bound">x</a> <a id="32448" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">⦂</a> <a id="32450" href="plfa.part2.Lambda.html#32400" class="Bound">A</a>

  <a id="_∋_⦂_.S"></a><a id="32455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32455" class="InductiveConstructor">S</a> <a id="32457" class="Symbol">:</a> <a id="32459" class="Symbol">∀</a> <a id="32461" class="Symbol">{</a><a id="32462" href="plfa.part2.Lambda.html#32462" class="Bound">Γ</a> <a id="32464" href="plfa.part2.Lambda.html#32464" class="Bound">x</a> <a id="32466" href="plfa.part2.Lambda.html#32466" class="Bound">y</a> <a id="32468" href="plfa.part2.Lambda.html#32468" class="Bound">A</a> <a id="32470" href="plfa.part2.Lambda.html#32470" class="Bound">B</a><a id="32471" class="Symbol">}</a>
    <a id="32477" class="Symbol">→</a> <a id="32479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32464" class="Bound">x</a> <a id="32481" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="32483" href="plfa.part2.Lambda.html#32466" class="Bound">y</a>
    <a id="32489" class="Symbol">→</a> <a id="32491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32462" class="Bound">Γ</a> <a id="32493" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">∋</a> <a id="32495" href="plfa.part2.Lambda.html#32464" class="Bound">x</a> <a id="32497" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">⦂</a> <a id="32499" href="plfa.part2.Lambda.html#32468" class="Bound">A</a>
      <a id="32507" class="Comment">------------------</a>
    <a id="32530" class="Symbol">→</a> <a id="32532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32462" class="Bound">Γ</a> <a id="32534" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">,</a> <a id="32536" href="plfa.part2.Lambda.html#32466" class="Bound">y</a> <a id="32538" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">⦂</a> <a id="32540" href="plfa.part2.Lambda.html#32470" class="Bound">B</a> <a id="32542" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">∋</a> <a id="32544" href="plfa.part2.Lambda.html#32464" class="Bound">x</a> <a id="32546" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">⦂</a> <a id="32548" href="plfa.part2.Lambda.html#32468" class="Bound">A</a>
</pre>{% endraw %}
The constructors `Z` and `S` correspond roughly to the constructors
`here` and `there` for the element-of relation `_∈_` on lists.
Constructor `S` takes an additional parameter, which ensures that
when we look up a variable that it is not _shadowed_ by another
variable with the same name to its left in the list.

### Typing judgment

The second judgment is written

    Γ ⊢ M ⦂ A

and indicates in context `Γ` that term `M` has type `A`.
Context `Γ` provides types for all the free variables in `M`.
For example:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

Typing is formalised as follows:
{% raw %}<pre class="Agda"><a id="33488" class="Keyword">infix</a>  <a id="33495" class="Number">4</a>  <a id="33498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33510" class="Datatype Operator">_⊢_⦂_</a>

<a id="33505" class="Keyword">data</a> <a id="_⊢_⦂_"></a><a id="33510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33510" class="Datatype Operator">_⊢_⦂_</a> <a id="33516" class="Symbol">:</a> <a id="33518" href="plfa.part2.Lambda.html#31112" class="Datatype">Context</a> <a id="33526" class="Symbol">→</a> <a id="33528" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="33533" class="Symbol">→</a> <a id="33535" href="plfa.part2.Lambda.html#29454" class="Datatype">Type</a> <a id="33540" class="Symbol">→</a> <a id="33542" class="PrimitiveType">Set</a> <a id="33546" class="Keyword">where</a>

  <a id="33555" class="Comment">-- Axiom</a>
  <a id="_⊢_⦂_.⊢`"></a><a id="33566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33566" class="InductiveConstructor">⊢`</a> <a id="33569" class="Symbol">:</a> <a id="33571" class="Symbol">∀</a> <a id="33573" class="Symbol">{</a><a id="33574" href="plfa.part2.Lambda.html#33574" class="Bound">Γ</a> <a id="33576" href="plfa.part2.Lambda.html#33576" class="Bound">x</a> <a id="33578" href="plfa.part2.Lambda.html#33578" class="Bound">A</a><a id="33579" class="Symbol">}</a>
    <a id="33585" class="Symbol">→</a> <a id="33587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33574" class="Bound">Γ</a> <a id="33589" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">∋</a> <a id="33591" href="plfa.part2.Lambda.html#33576" class="Bound">x</a> <a id="33593" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">⦂</a> <a id="33595" href="plfa.part2.Lambda.html#33578" class="Bound">A</a>
      <a id="33603" class="Comment">-----------</a>
    <a id="33619" class="Symbol">→</a> <a id="33621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33574" class="Bound">Γ</a> <a id="33623" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="33625" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="33627" href="plfa.part2.Lambda.html#33576" class="Bound">x</a> <a id="33629" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="33631" href="plfa.part2.Lambda.html#33578" class="Bound">A</a>

  <a id="33636" class="Comment">-- ⇒-I</a>
  <a id="_⊢_⦂_.⊢ƛ"></a><a id="33645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33645" class="InductiveConstructor">⊢ƛ</a> <a id="33648" class="Symbol">:</a> <a id="33650" class="Symbol">∀</a> <a id="33652" class="Symbol">{</a><a id="33653" href="plfa.part2.Lambda.html#33653" class="Bound">Γ</a> <a id="33655" href="plfa.part2.Lambda.html#33655" class="Bound">x</a> <a id="33657" href="plfa.part2.Lambda.html#33657" class="Bound">N</a> <a id="33659" href="plfa.part2.Lambda.html#33659" class="Bound">A</a> <a id="33661" href="plfa.part2.Lambda.html#33661" class="Bound">B</a><a id="33662" class="Symbol">}</a>
    <a id="33668" class="Symbol">→</a> <a id="33670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33653" class="Bound">Γ</a> <a id="33672" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">,</a> <a id="33674" href="plfa.part2.Lambda.html#33655" class="Bound">x</a> <a id="33676" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">⦂</a> <a id="33678" href="plfa.part2.Lambda.html#33659" class="Bound">A</a> <a id="33680" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="33682" href="plfa.part2.Lambda.html#33657" class="Bound">N</a> <a id="33684" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="33686" href="plfa.part2.Lambda.html#33661" class="Bound">B</a>
      <a id="33694" class="Comment">-------------------</a>
    <a id="33718" class="Symbol">→</a> <a id="33720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33653" class="Bound">Γ</a> <a id="33722" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="33724" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="33726" href="plfa.part2.Lambda.html#33655" class="Bound">x</a> <a id="33728" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="33730" href="plfa.part2.Lambda.html#33657" class="Bound">N</a> <a id="33732" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="33734" href="plfa.part2.Lambda.html#33659" class="Bound">A</a> <a id="33736" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="33738" href="plfa.part2.Lambda.html#33661" class="Bound">B</a>

  <a id="33743" class="Comment">-- ⇒-E</a>
  <a id="_⊢_⦂_._·_"></a><a id="33752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33752" class="InductiveConstructor Operator">_·_</a> <a id="33756" class="Symbol">:</a> <a id="33758" class="Symbol">∀</a> <a id="33760" class="Symbol">{</a><a id="33761" href="plfa.part2.Lambda.html#33761" class="Bound">Γ</a> <a id="33763" href="plfa.part2.Lambda.html#33763" class="Bound">L</a> <a id="33765" href="plfa.part2.Lambda.html#33765" class="Bound">M</a> <a id="33767" href="plfa.part2.Lambda.html#33767" class="Bound">A</a> <a id="33769" href="plfa.part2.Lambda.html#33769" class="Bound">B</a><a id="33770" class="Symbol">}</a>
    <a id="33776" class="Symbol">→</a> <a id="33778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33761" class="Bound">Γ</a> <a id="33780" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="33782" href="plfa.part2.Lambda.html#33763" class="Bound">L</a> <a id="33784" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="33786" href="plfa.part2.Lambda.html#33767" class="Bound">A</a> <a id="33788" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="33790" href="plfa.part2.Lambda.html#33769" class="Bound">B</a>
    <a id="33796" class="Symbol">→</a> <a id="33798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33761" class="Bound">Γ</a> <a id="33800" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="33802" href="plfa.part2.Lambda.html#33765" class="Bound">M</a> <a id="33804" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="33806" href="plfa.part2.Lambda.html#33767" class="Bound">A</a>
      <a id="33814" class="Comment">-------------</a>
    <a id="33832" class="Symbol">→</a> <a id="33834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33761" class="Bound">Γ</a> <a id="33836" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="33838" href="plfa.part2.Lambda.html#33763" class="Bound">L</a> <a id="33840" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="33842" href="plfa.part2.Lambda.html#33765" class="Bound">M</a> <a id="33844" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="33846" href="plfa.part2.Lambda.html#33769" class="Bound">B</a>

  <a id="33851" class="Comment">-- ℕ-I₁</a>
  <a id="_⊢_⦂_.⊢zero"></a><a id="33861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33861" class="InductiveConstructor">⊢zero</a> <a id="33867" class="Symbol">:</a> <a id="33869" class="Symbol">∀</a> <a id="33871" class="Symbol">{</a><a id="33872" href="plfa.part2.Lambda.html#33872" class="Bound">Γ</a><a id="33873" class="Symbol">}</a>
      <a id="33881" class="Comment">--------------</a>
    <a id="33900" class="Symbol">→</a> <a id="33902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33872" class="Bound">Γ</a> <a id="33904" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="33906" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="33912" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="33914" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a>

  <a id="33920" class="Comment">-- ℕ-I₂</a>
  <a id="_⊢_⦂_.⊢suc"></a><a id="33930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33930" class="InductiveConstructor">⊢suc</a> <a id="33935" class="Symbol">:</a> <a id="33937" class="Symbol">∀</a> <a id="33939" class="Symbol">{</a><a id="33940" href="plfa.part2.Lambda.html#33940" class="Bound">Γ</a> <a id="33942" href="plfa.part2.Lambda.html#33942" class="Bound">M</a><a id="33943" class="Symbol">}</a>
    <a id="33949" class="Symbol">→</a> <a id="33951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33940" class="Bound">Γ</a> <a id="33953" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="33955" href="plfa.part2.Lambda.html#33942" class="Bound">M</a> <a id="33957" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="33959" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a>
      <a id="33968" class="Comment">---------------</a>
    <a id="33988" class="Symbol">→</a> <a id="33990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33940" class="Bound">Γ</a> <a id="33992" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="33994" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="33999" href="plfa.part2.Lambda.html#33942" class="Bound">M</a> <a id="34001" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="34003" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a>

  <a id="34009" class="Comment">-- ℕ-E</a>
  <a id="_⊢_⦂_.⊢case"></a><a id="34018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34018" class="InductiveConstructor">⊢case</a> <a id="34024" class="Symbol">:</a> <a id="34026" class="Symbol">∀</a> <a id="34028" class="Symbol">{</a><a id="34029" href="plfa.part2.Lambda.html#34029" class="Bound">Γ</a> <a id="34031" href="plfa.part2.Lambda.html#34031" class="Bound">L</a> <a id="34033" href="plfa.part2.Lambda.html#34033" class="Bound">M</a> <a id="34035" href="plfa.part2.Lambda.html#34035" class="Bound">x</a> <a id="34037" href="plfa.part2.Lambda.html#34037" class="Bound">N</a> <a id="34039" href="plfa.part2.Lambda.html#34039" class="Bound">A</a><a id="34040" class="Symbol">}</a>
    <a id="34046" class="Symbol">→</a> <a id="34048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34029" class="Bound">Γ</a> <a id="34050" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="34052" href="plfa.part2.Lambda.html#34031" class="Bound">L</a> <a id="34054" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="34056" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a>
    <a id="34063" class="Symbol">→</a> <a id="34065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34029" class="Bound">Γ</a> <a id="34067" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="34069" href="plfa.part2.Lambda.html#34033" class="Bound">M</a> <a id="34071" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="34073" href="plfa.part2.Lambda.html#34039" class="Bound">A</a>
    <a id="34079" class="Symbol">→</a> <a id="34081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34029" class="Bound">Γ</a> <a id="34083" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">,</a> <a id="34085" href="plfa.part2.Lambda.html#34035" class="Bound">x</a> <a id="34087" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">⦂</a> <a id="34089" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a> <a id="34092" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="34094" href="plfa.part2.Lambda.html#34037" class="Bound">N</a> <a id="34096" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="34098" href="plfa.part2.Lambda.html#34039" class="Bound">A</a>
      <a id="34106" class="Comment">-------------------------------------</a>
    <a id="34148" class="Symbol">→</a> <a id="34150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34029" class="Bound">Γ</a> <a id="34152" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="34154" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="34159" href="plfa.part2.Lambda.html#34031" class="Bound">L</a> <a id="34161" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="34168" href="plfa.part2.Lambda.html#34033" class="Bound">M</a> <a id="34170" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="34175" href="plfa.part2.Lambda.html#34035" class="Bound">x</a> <a id="34177" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="34179" href="plfa.part2.Lambda.html#34037" class="Bound">N</a> <a id="34181" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="34183" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="34185" href="plfa.part2.Lambda.html#34039" class="Bound">A</a>

  <a id="_⊢_⦂_.⊢μ"></a><a id="34190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34190" class="InductiveConstructor">⊢μ</a> <a id="34193" class="Symbol">:</a> <a id="34195" class="Symbol">∀</a> <a id="34197" class="Symbol">{</a><a id="34198" href="plfa.part2.Lambda.html#34198" class="Bound">Γ</a> <a id="34200" href="plfa.part2.Lambda.html#34200" class="Bound">x</a> <a id="34202" href="plfa.part2.Lambda.html#34202" class="Bound">M</a> <a id="34204" href="plfa.part2.Lambda.html#34204" class="Bound">A</a><a id="34205" class="Symbol">}</a>
    <a id="34211" class="Symbol">→</a> <a id="34213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34198" class="Bound">Γ</a> <a id="34215" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">,</a> <a id="34217" href="plfa.part2.Lambda.html#34200" class="Bound">x</a> <a id="34219" href="plfa.part2.Lambda.html#31152" class="InductiveConstructor Operator">⦂</a> <a id="34221" href="plfa.part2.Lambda.html#34204" class="Bound">A</a> <a id="34223" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="34225" href="plfa.part2.Lambda.html#34202" class="Bound">M</a> <a id="34227" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="34229" href="plfa.part2.Lambda.html#34204" class="Bound">A</a>
      <a id="34237" class="Comment">-----------------</a>
    <a id="34259" class="Symbol">→</a> <a id="34261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34198" class="Bound">Γ</a> <a id="34263" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="34265" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="34267" href="plfa.part2.Lambda.html#34200" class="Bound">x</a> <a id="34269" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="34271" href="plfa.part2.Lambda.html#34202" class="Bound">M</a> <a id="34273" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="34275" href="plfa.part2.Lambda.html#34204" class="Bound">A</a>
</pre>{% endraw %}
Each type rule is named after the constructor for the
corresponding term.

Most of the rules have a second name, derived from a convention in
logic, whereby the rule is named after the type connective that it
concerns; rules to introduce and to eliminate each connective are
labeled `-I` and `-E`, respectively. As we read the rules from top to
bottom, introduction and elimination rules do what they say on the
tin: the first _introduces_ a formula for the connective, which
appears in the conclusion but not in the premises; while the second
_eliminates_ a formula for the connective, which appears in a premise
but not in the conclusion. An introduction rule describes how to
construct a value of the type (abstractions yield functions, successor
and zero yield naturals), while an elimination rule describes how to
deconstruct a value of the given type (applications use functions,
case expressions use naturals).

Note also the three places (in `⊢ƛ`, `⊢case`, and `⊢μ`) where the
context is extended with `x` and an appropriate type, corresponding to
the three places where a bound variable is introduced.

The rules are deterministic, in that at most one rule applies to every term.


### Checking inequality and postulating the impossible {#impossible}

The following function makes it convenient to assert an inequality:
{% raw %}<pre class="Agda"><a id="_≠_"></a><a id="35615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35615" class="Function Operator">_≠_</a> <a id="35619" class="Symbol">:</a> <a id="35621" class="Symbol">∀</a> <a id="35623" class="Symbol">(</a><a id="35624" href="plfa.part2.Lambda.html#35624" class="Bound">x</a> <a id="35626" href="plfa.part2.Lambda.html#35626" class="Bound">y</a> <a id="35628" class="Symbol">:</a> <a id="35630" href="plfa.part2.Lambda.html#3695" class="Function">Id</a><a id="35632" class="Symbol">)</a> <a id="35634" class="Symbol">→</a> <a id="35636" href="plfa.part2.Lambda.html#35624" class="Bound">x</a> <a id="35638" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="35640" href="plfa.part2.Lambda.html#35626" class="Bound">y</a>
<a id="35642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35642" class="Bound">x</a> <a id="35644" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="35646" href="plfa.part2.Lambda.html#35646" class="Bound">y</a>  <a id="35649" class="Keyword">with</a> <a id="35654" href="plfa.part2.Lambda.html#35642" class="Bound">x</a> <a id="35656" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="35658" href="plfa.part2.Lambda.html#35646" class="Bound">y</a>
<a id="35660" class="Symbol">...</a>       <a id="35670" class="Symbol">|</a> <a id="35672" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="35676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35676" class="Bound">x≢y</a>  <a id="35681" class="Symbol">=</a>  <a id="35684" href="plfa.part2.Lambda.html#35676" class="Bound">x≢y</a>
<a id="35688" class="Symbol">...</a>       <a id="35698" class="Symbol">|</a> <a id="35700" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="35704" class="Symbol">_</a>    <a id="35709" class="Symbol">=</a>  <a id="35712" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="35719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35748" class="Postulate">impossible</a>
  <a id="35732" class="Keyword">where</a> <a id="35738" class="Keyword">postulate</a> <a id="35748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35748" class="Postulate">impossible</a> <a id="35759" class="Symbol">:</a> <a id="35761" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}Here `_≟_` is the function that tests two identifiers for equality.
We intend to apply the function only when the
two arguments are indeed unequal, and indicate that the second
case should never arise by postulating a term `impossible` of
the empty type `⊥`.  If we use C-c C-n to normalise the term

    "a" ≠ "a"

Agda will return an answer warning us that the impossible has occurred:

    ⊥-elim (.plfa.Lambda.impossible "a" "a" refl)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.


### Example type derivations {#derivation}

Type derivations correspond to trees. In informal notation, here
is a type derivation for the Church numeral two,

                            ∋s                     ∋z
                            ------------------ ⊢`  -------------- ⊢`
    ∋s                      Γ₂ ⊢ ` "s" ⦂ A ⇒ A     Γ₂ ⊢ ` "z" ⦂ A
    ------------------ ⊢`   ------------------------------------- _·_
    Γ₂ ⊢ ` "s" ⦂ A ⇒ A      Γ₂ ⊢ ` "s" · ` "z" ⦂ A
    ---------------------------------------------- _·_
    Γ₂ ⊢ ` "s" · (` "s" · ` "z") ⦂ A
    -------------------------------------------- ⊢ƛ
    Γ₁ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ A ⇒ A
    ------------------------------------------------------------- ⊢ƛ
    Γ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ (A ⇒ A) ⇒ A ⇒ A

where `∋s` and `∋z` abbreviate the two derivations,

                 ---------------- Z
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
    ----------------------------- S       ------------- Z
    Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where `Γ₁ = Γ , "s" ⦂ A ⇒ A` and `Γ₂ = Γ , "s" ⦂ A ⇒ A , "z" ⦂ A`.
The typing derivation is valid for any `Γ` and `A`, for instance,
we might take `Γ` to be `∅` and `A` to be `` `ℕ ``.

Here is the above typing derivation formalised in Agda:
{% raw %}<pre class="Agda"><a id="Ch"></a><a id="37694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37694" class="Function">Ch</a> <a id="37697" class="Symbol">:</a> <a id="37699" href="plfa.part2.Lambda.html#29454" class="Datatype">Type</a> <a id="37704" class="Symbol">→</a> <a id="37706" href="plfa.part2.Lambda.html#29454" class="Datatype">Type</a>
<a id="37711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37694" class="Function">Ch</a> <a id="37714" href="plfa.part2.Lambda.html#37714" class="Bound">A</a> <a id="37716" class="Symbol">=</a> <a id="37718" class="Symbol">(</a><a id="37719" href="plfa.part2.Lambda.html#37714" class="Bound">A</a> <a id="37721" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="37723" href="plfa.part2.Lambda.html#37714" class="Bound">A</a><a id="37724" class="Symbol">)</a> <a id="37726" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="37728" href="plfa.part2.Lambda.html#37714" class="Bound">A</a> <a id="37730" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="37732" href="plfa.part2.Lambda.html#37714" class="Bound">A</a>

<a id="⊢twoᶜ"></a><a id="37735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37735" class="Function">⊢twoᶜ</a> <a id="37741" class="Symbol">:</a> <a id="37743" class="Symbol">∀</a> <a id="37745" class="Symbol">{</a><a id="37746" href="plfa.part2.Lambda.html#37746" class="Bound">Γ</a> <a id="37748" href="plfa.part2.Lambda.html#37748" class="Bound">A</a><a id="37749" class="Symbol">}</a> <a id="37751" class="Symbol">→</a> <a id="37753" href="plfa.part2.Lambda.html#37746" class="Bound">Γ</a> <a id="37755" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="37757" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="37762" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="37764" href="plfa.part2.Lambda.html#37694" class="Function">Ch</a> <a id="37767" href="plfa.part2.Lambda.html#37748" class="Bound">A</a>
<a id="37769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37735" class="Function">⊢twoᶜ</a> <a id="37775" class="Symbol">=</a> <a id="37777" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="37780" class="Symbol">(</a><a id="37781" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="37784" class="Symbol">(</a><a id="37785" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="37788" href="plfa.part2.Lambda.html#37821" class="Function">∋s</a> <a id="37791" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="37793" class="Symbol">(</a><a id="37794" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="37797" href="plfa.part2.Lambda.html#37821" class="Function">∋s</a> <a id="37800" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="37802" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="37805" href="plfa.part2.Lambda.html#37844" class="Function">∋z</a><a id="37807" class="Symbol">)))</a>
  <a id="37813" class="Keyword">where</a>
  <a id="37821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37821" class="Function">∋s</a> <a id="37824" class="Symbol">=</a> <a id="37826" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="37828" class="Symbol">(</a><a id="37829" class="String">&quot;s&quot;</a> <a id="37833" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="37835" class="String">&quot;z&quot;</a><a id="37838" class="Symbol">)</a> <a id="37840" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>
  <a id="37844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37844" class="Function">∋z</a> <a id="37847" class="Symbol">=</a> <a id="37849" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>
</pre>{% endraw %}
Here are the typings corresponding to computing two plus two:
{% raw %}<pre class="Agda"><a id="⊢two"></a><a id="37922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37922" class="Function">⊢two</a> <a id="37927" class="Symbol">:</a> <a id="37929" class="Symbol">∀</a> <a id="37931" class="Symbol">{</a><a id="37932" href="plfa.part2.Lambda.html#37932" class="Bound">Γ</a><a id="37933" class="Symbol">}</a> <a id="37935" class="Symbol">→</a> <a id="37937" href="plfa.part2.Lambda.html#37932" class="Bound">Γ</a> <a id="37939" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="37941" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37945" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="37947" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a>
<a id="37950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37922" class="Function">⊢two</a> <a id="37955" class="Symbol">=</a> <a id="37957" href="plfa.part2.Lambda.html#33930" class="InductiveConstructor">⊢suc</a> <a id="37962" class="Symbol">(</a><a id="37963" href="plfa.part2.Lambda.html#33930" class="InductiveConstructor">⊢suc</a> <a id="37968" href="plfa.part2.Lambda.html#33861" class="InductiveConstructor">⊢zero</a><a id="37973" class="Symbol">)</a>

<a id="⊢plus"></a><a id="37976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37976" class="Function">⊢plus</a> <a id="37982" class="Symbol">:</a> <a id="37984" class="Symbol">∀</a> <a id="37986" class="Symbol">{</a><a id="37987" href="plfa.part2.Lambda.html#37987" class="Bound">Γ</a><a id="37988" class="Symbol">}</a> <a id="37990" class="Symbol">→</a> <a id="37992" href="plfa.part2.Lambda.html#37987" class="Bound">Γ</a> <a id="37994" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="37996" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="38001" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="38003" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a> <a id="38006" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="38008" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a> <a id="38011" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="38013" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a>
<a id="38016" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37976" class="Function">⊢plus</a> <a id="38022" class="Symbol">=</a> <a id="38024" href="plfa.part2.Lambda.html#34190" class="InductiveConstructor">⊢μ</a> <a id="38027" class="Symbol">(</a><a id="38028" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="38031" class="Symbol">(</a><a id="38032" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="38035" class="Symbol">(</a><a id="38036" href="plfa.part2.Lambda.html#34018" class="InductiveConstructor">⊢case</a> <a id="38042" class="Symbol">(</a><a id="38043" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="38046" href="plfa.part2.Lambda.html#38171" class="Function">∋m</a><a id="38048" class="Symbol">)</a> <a id="38050" class="Symbol">(</a><a id="38051" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="38054" href="plfa.part2.Lambda.html#38197" class="Function">∋n</a><a id="38056" class="Symbol">)</a>
         <a id="38067" class="Symbol">(</a><a id="38068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33930" class="InductiveConstructor">⊢suc</a> <a id="38073" class="Symbol">(</a><a id="38074" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="38077" href="plfa.part2.Lambda.html#38113" class="Function">∋+</a> <a id="38080" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="38082" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="38085" href="plfa.part2.Lambda.html#38207" class="Function">∋m′</a> <a id="38089" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="38091" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="38094" href="plfa.part2.Lambda.html#38217" class="Function">∋n′</a><a id="38097" class="Symbol">)))))</a>
  <a id="38105" class="Keyword">where</a>
  <a id="38113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38113" class="Function">∋+</a>  <a id="38117" class="Symbol">=</a> <a id="38119" class="Symbol">(</a><a id="38120" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="38122" class="Symbol">(</a><a id="38123" class="String">&quot;+&quot;</a> <a id="38127" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="38129" class="String">&quot;m&quot;</a><a id="38132" class="Symbol">)</a> <a id="38134" class="Symbol">(</a><a id="38135" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="38137" class="Symbol">(</a><a id="38138" class="String">&quot;+&quot;</a> <a id="38142" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="38144" class="String">&quot;n&quot;</a><a id="38147" class="Symbol">)</a> <a id="38149" class="Symbol">(</a><a id="38150" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="38152" class="Symbol">(</a><a id="38153" class="String">&quot;+&quot;</a> <a id="38157" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="38159" class="String">&quot;m&quot;</a><a id="38162" class="Symbol">)</a> <a id="38164" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a><a id="38165" class="Symbol">)))</a>
  <a id="38171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38171" class="Function">∋m</a>  <a id="38175" class="Symbol">=</a> <a id="38177" class="Symbol">(</a><a id="38178" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="38180" class="Symbol">(</a><a id="38181" class="String">&quot;m&quot;</a> <a id="38185" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="38187" class="String">&quot;n&quot;</a><a id="38190" class="Symbol">)</a> <a id="38192" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a><a id="38193" class="Symbol">)</a>
  <a id="38197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38197" class="Function">∋n</a>  <a id="38201" class="Symbol">=</a> <a id="38203" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>
  <a id="38207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38207" class="Function">∋m′</a> <a id="38211" class="Symbol">=</a> <a id="38213" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>
  <a id="38217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38217" class="Function">∋n′</a> <a id="38221" class="Symbol">=</a> <a id="38223" class="Symbol">(</a><a id="38224" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="38226" class="Symbol">(</a><a id="38227" class="String">&quot;n&quot;</a> <a id="38231" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="38233" class="String">&quot;m&quot;</a><a id="38236" class="Symbol">)</a> <a id="38238" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a><a id="38239" class="Symbol">)</a>

<a id="⊢2+2"></a><a id="38242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38242" class="Function">⊢2+2</a> <a id="38247" class="Symbol">:</a> <a id="38249" href="plfa.part2.Lambda.html#31134" class="InductiveConstructor">∅</a> <a id="38251" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="38253" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="38258" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38260" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="38264" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38266" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="38270" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="38272" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a>
<a id="38275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38242" class="Function">⊢2+2</a> <a id="38280" class="Symbol">=</a> <a id="38282" href="plfa.part2.Lambda.html#37976" class="Function">⊢plus</a> <a id="38288" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="38290" href="plfa.part2.Lambda.html#37922" class="Function">⊢two</a> <a id="38295" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="38297" href="plfa.part2.Lambda.html#37922" class="Function">⊢two</a>
</pre>{% endraw %}In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where "n" is the last binding in the context, and
the second after "m" is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
{% raw %}<pre class="Agda"><a id="⊢plusᶜ"></a><a id="38944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38944" class="Function">⊢plusᶜ</a> <a id="38951" class="Symbol">:</a> <a id="38953" class="Symbol">∀</a> <a id="38955" class="Symbol">{</a><a id="38956" href="plfa.part2.Lambda.html#38956" class="Bound">Γ</a> <a id="38958" href="plfa.part2.Lambda.html#38958" class="Bound">A</a><a id="38959" class="Symbol">}</a> <a id="38961" class="Symbol">→</a> <a id="38963" href="plfa.part2.Lambda.html#38956" class="Bound">Γ</a>  <a id="38966" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="38968" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="38974" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="38976" href="plfa.part2.Lambda.html#37694" class="Function">Ch</a> <a id="38979" href="plfa.part2.Lambda.html#38958" class="Bound">A</a> <a id="38981" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="38983" href="plfa.part2.Lambda.html#37694" class="Function">Ch</a> <a id="38986" href="plfa.part2.Lambda.html#38958" class="Bound">A</a> <a id="38988" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="38990" href="plfa.part2.Lambda.html#37694" class="Function">Ch</a> <a id="38993" href="plfa.part2.Lambda.html#38958" class="Bound">A</a>
<a id="38995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38944" class="Function">⊢plusᶜ</a> <a id="39002" class="Symbol">=</a> <a id="39004" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="39007" class="Symbol">(</a><a id="39008" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="39011" class="Symbol">(</a><a id="39012" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="39015" class="Symbol">(</a><a id="39016" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="39019" class="Symbol">(</a><a id="39020" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="39023" href="plfa.part2.Lambda.html#39074" class="Function">∋m</a> <a id="39026" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="39028" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="39031" href="plfa.part2.Lambda.html#39168" class="Function">∋s</a> <a id="39034" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="39036" class="Symbol">(</a><a id="39037" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="39040" href="plfa.part2.Lambda.html#39129" class="Function">∋n</a> <a id="39043" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="39045" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="39048" href="plfa.part2.Lambda.html#39168" class="Function">∋s</a> <a id="39051" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="39053" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="39056" href="plfa.part2.Lambda.html#39191" class="Function">∋z</a><a id="39058" class="Symbol">)))))</a>
  <a id="39066" class="Keyword">where</a>
  <a id="39074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39074" class="Function">∋m</a> <a id="39077" class="Symbol">=</a> <a id="39079" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="39081" class="Symbol">(</a><a id="39082" class="String">&quot;m&quot;</a> <a id="39086" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="39088" class="String">&quot;z&quot;</a><a id="39091" class="Symbol">)</a> <a id="39093" class="Symbol">(</a><a id="39094" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="39096" class="Symbol">(</a><a id="39097" class="String">&quot;m&quot;</a> <a id="39101" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="39103" class="String">&quot;s&quot;</a><a id="39106" class="Symbol">)</a> <a id="39108" class="Symbol">(</a><a id="39109" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="39111" class="Symbol">(</a><a id="39112" class="String">&quot;m&quot;</a> <a id="39116" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="39118" class="String">&quot;n&quot;</a><a id="39121" class="Symbol">)</a> <a id="39123" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a><a id="39124" class="Symbol">))</a>
  <a id="39129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39129" class="Function">∋n</a> <a id="39132" class="Symbol">=</a> <a id="39134" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="39136" class="Symbol">(</a><a id="39137" class="String">&quot;n&quot;</a> <a id="39141" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="39143" class="String">&quot;z&quot;</a><a id="39146" class="Symbol">)</a> <a id="39148" class="Symbol">(</a><a id="39149" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="39151" class="Symbol">(</a><a id="39152" class="String">&quot;n&quot;</a> <a id="39156" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="39158" class="String">&quot;s&quot;</a><a id="39161" class="Symbol">)</a> <a id="39163" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a><a id="39164" class="Symbol">)</a>
  <a id="39168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39168" class="Function">∋s</a> <a id="39171" class="Symbol">=</a> <a id="39173" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="39175" class="Symbol">(</a><a id="39176" class="String">&quot;s&quot;</a> <a id="39180" href="plfa.part2.Lambda.html#35615" class="Function Operator">≠</a> <a id="39182" class="String">&quot;z&quot;</a><a id="39185" class="Symbol">)</a> <a id="39187" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>
  <a id="39191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39191" class="Function">∋z</a> <a id="39194" class="Symbol">=</a> <a id="39196" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>

<a id="⊢sucᶜ"></a><a id="39199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39199" class="Function">⊢sucᶜ</a> <a id="39205" class="Symbol">:</a> <a id="39207" class="Symbol">∀</a> <a id="39209" class="Symbol">{</a><a id="39210" href="plfa.part2.Lambda.html#39210" class="Bound">Γ</a><a id="39211" class="Symbol">}</a> <a id="39213" class="Symbol">→</a> <a id="39215" href="plfa.part2.Lambda.html#39210" class="Bound">Γ</a> <a id="39217" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="39219" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="39224" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="39226" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a> <a id="39229" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="39231" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a>
<a id="39234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39199" class="Function">⊢sucᶜ</a> <a id="39240" class="Symbol">=</a> <a id="39242" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="39245" class="Symbol">(</a><a id="39246" href="plfa.part2.Lambda.html#33930" class="InductiveConstructor">⊢suc</a> <a id="39251" class="Symbol">(</a><a id="39252" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="39255" href="plfa.part2.Lambda.html#39270" class="Function">∋n</a><a id="39257" class="Symbol">))</a>
  <a id="39262" class="Keyword">where</a>
  <a id="39270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39270" class="Function">∋n</a> <a id="39273" class="Symbol">=</a> <a id="39275" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>

<a id="⊢2+2ᶜ"></a><a id="39278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39278" class="Function">⊢2+2ᶜ</a> <a id="39284" class="Symbol">:</a> <a id="39286" href="plfa.part2.Lambda.html#31134" class="InductiveConstructor">∅</a> <a id="39288" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="39290" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="39296" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="39298" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="39303" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="39305" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="39310" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="39312" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="39317" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="39319" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="39325" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="39327" href="plfa.part2.Lambda.html#29500" class="InductiveConstructor">`ℕ</a>
<a id="39330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39278" class="Function">⊢2+2ᶜ</a> <a id="39336" class="Symbol">=</a> <a id="39338" href="plfa.part2.Lambda.html#38944" class="Function">⊢plusᶜ</a> <a id="39345" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="39347" href="plfa.part2.Lambda.html#37735" class="Function">⊢twoᶜ</a> <a id="39353" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="39355" href="plfa.part2.Lambda.html#37735" class="Function">⊢twoᶜ</a> <a id="39361" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="39363" href="plfa.part2.Lambda.html#39199" class="Function">⊢sucᶜ</a> <a id="39369" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="39371" href="plfa.part2.Lambda.html#33861" class="InductiveConstructor">⊢zero</a>
</pre>{% endraw %}
### Interaction with Agda

Construction of a type derivation may be done interactively.
Start with the declaration:

    ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
    ⊢sucᶜ = ?

Typing C-c C-l causes Agda to create a hole and tell us its expected type:

    ⊢sucᶜ = { }0
    ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `sucᶜ` is `ƛ`, which is typed using `⊢ƛ`. The
`⊢ƛ` rule in turn takes one argument, which Agda leaves as a hole:

    ⊢sucᶜ = ⊢ƛ { }1
    ?1 : ∅ , "n" ⦂ `ℕ ⊢ `suc ` "n" ⦂ `ℕ

We can fill in the hole by typing C-c C-r again:

    ⊢sucᶜ = ⊢ƛ (⊢suc { }2)
    ?2 : ∅ , "n" ⦂ `ℕ ⊢ ` "n" ⦂ `ℕ

And again:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` { }3))
    ?3 : ∅ , "n" ⦂ `ℕ ∋ "n" ⦂ `ℕ

A further attempt with C-c C-r yields the message:

    Don't know which constructor to introduce of Z or S

We can fill in `Z` by hand. If we type C-c C-space, Agda will confirm we are done:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` Z))

The entire process can be automated using Agsy, invoked with C-c C-a.

Chapter [Inference]({{ site.baseurl }}/Inference/)
will show how to use Agda to compute type derivations directly.


### Lookup is injective

The lookup relation `Γ ∋ x ⦂ A` is injective, in that for each `Γ` and `x`
there is at most one `A` such that the judgment holds:
{% raw %}<pre class="Agda"><a id="∋-injective"></a><a id="40687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40687" class="Function">∋-injective</a> <a id="40699" class="Symbol">:</a> <a id="40701" class="Symbol">∀</a> <a id="40703" class="Symbol">{</a><a id="40704" href="plfa.part2.Lambda.html#40704" class="Bound">Γ</a> <a id="40706" href="plfa.part2.Lambda.html#40706" class="Bound">x</a> <a id="40708" href="plfa.part2.Lambda.html#40708" class="Bound">A</a> <a id="40710" href="plfa.part2.Lambda.html#40710" class="Bound">B</a><a id="40711" class="Symbol">}</a> <a id="40713" class="Symbol">→</a> <a id="40715" href="plfa.part2.Lambda.html#40704" class="Bound">Γ</a> <a id="40717" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">∋</a> <a id="40719" href="plfa.part2.Lambda.html#40706" class="Bound">x</a> <a id="40721" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">⦂</a> <a id="40723" href="plfa.part2.Lambda.html#40708" class="Bound">A</a> <a id="40725" class="Symbol">→</a> <a id="40727" href="plfa.part2.Lambda.html#40704" class="Bound">Γ</a> <a id="40729" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">∋</a> <a id="40731" href="plfa.part2.Lambda.html#40706" class="Bound">x</a> <a id="40733" href="plfa.part2.Lambda.html#32346" class="Datatype Operator">⦂</a> <a id="40735" href="plfa.part2.Lambda.html#40710" class="Bound">B</a> <a id="40737" class="Symbol">→</a> <a id="40739" href="plfa.part2.Lambda.html#40708" class="Bound">A</a> <a id="40741" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="40743" href="plfa.part2.Lambda.html#40710" class="Bound">B</a>
<a id="40745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40687" class="Function">∋-injective</a> <a id="40757" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>        <a id="40766" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>          <a id="40777" class="Symbol">=</a>  <a id="40780" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="40785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40687" class="Function">∋-injective</a> <a id="40797" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>        <a id="40806" class="Symbol">(</a><a id="40807" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="40809" href="plfa.part2.Lambda.html#40809" class="Bound">x≢</a> <a id="40812" class="Symbol">_)</a>   <a id="40817" class="Symbol">=</a>  <a id="40820" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40827" class="Symbol">(</a><a id="40828" href="plfa.part2.Lambda.html#40809" class="Bound">x≢</a> <a id="40831" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40835" class="Symbol">)</a>
<a id="40837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40687" class="Function">∋-injective</a> <a id="40849" class="Symbol">(</a><a id="40850" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="40852" href="plfa.part2.Lambda.html#40852" class="Bound">x≢</a> <a id="40855" class="Symbol">_)</a> <a id="40858" href="plfa.part2.Lambda.html#32389" class="InductiveConstructor">Z</a>          <a id="40869" class="Symbol">=</a>  <a id="40872" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40879" class="Symbol">(</a><a id="40880" href="plfa.part2.Lambda.html#40852" class="Bound">x≢</a> <a id="40883" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40887" class="Symbol">)</a>
<a id="40889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40687" class="Function">∋-injective</a> <a id="40901" class="Symbol">(</a><a id="40902" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="40904" class="Symbol">_</a> <a id="40906" href="plfa.part2.Lambda.html#40906" class="Bound">∋x</a><a id="40908" class="Symbol">)</a> <a id="40910" class="Symbol">(</a><a id="40911" href="plfa.part2.Lambda.html#32455" class="InductiveConstructor">S</a> <a id="40913" class="Symbol">_</a> <a id="40915" href="plfa.part2.Lambda.html#40915" class="Bound">∋x′</a><a id="40918" class="Symbol">)</a>  <a id="40921" class="Symbol">=</a>  <a id="40924" href="plfa.part2.Lambda.html#40687" class="Function">∋-injective</a> <a id="40936" href="plfa.part2.Lambda.html#40906" class="Bound">∋x</a> <a id="40939" href="plfa.part2.Lambda.html#40915" class="Bound">∋x′</a>
</pre>{% endraw %}
The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

{% raw %}<pre class="Agda"><a id="nope₁"></a><a id="41376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41376" class="Function">nope₁</a> <a id="41382" class="Symbol">:</a> <a id="41384" class="Symbol">∀</a> <a id="41386" class="Symbol">{</a><a id="41387" href="plfa.part2.Lambda.html#41387" class="Bound">A</a><a id="41388" class="Symbol">}</a> <a id="41390" class="Symbol">→</a> <a id="41392" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41394" class="Symbol">(</a><a id="41395" href="plfa.part2.Lambda.html#31134" class="InductiveConstructor">∅</a> <a id="41397" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="41399" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="41405" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="41407" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="41412" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="41418" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="41420" href="plfa.part2.Lambda.html#41387" class="Bound">A</a><a id="41421" class="Symbol">)</a>
<a id="41423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41376" class="Function">nope₁</a> <a id="41429" class="Symbol">(()</a> <a id="41433" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="41435" class="Symbol">_)</a>
</pre>{% endraw %}
As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

{% raw %}<pre class="Agda"><a id="nope₂"></a><a id="41640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41640" class="Function">nope₂</a> <a id="41646" class="Symbol">:</a> <a id="41648" class="Symbol">∀</a> <a id="41650" class="Symbol">{</a><a id="41651" href="plfa.part2.Lambda.html#41651" class="Bound">A</a><a id="41652" class="Symbol">}</a> <a id="41654" class="Symbol">→</a> <a id="41656" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41658" class="Symbol">(</a><a id="41659" href="plfa.part2.Lambda.html#31134" class="InductiveConstructor">∅</a> <a id="41661" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⊢</a> <a id="41663" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="41665" class="String">&quot;x&quot;</a> <a id="41669" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="41671" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="41673" class="String">&quot;x&quot;</a> <a id="41677" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="41679" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="41681" class="String">&quot;x&quot;</a> <a id="41685" href="plfa.part2.Lambda.html#33510" class="Datatype Operator">⦂</a> <a id="41687" href="plfa.part2.Lambda.html#41651" class="Bound">A</a><a id="41688" class="Symbol">)</a>
<a id="41690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41640" class="Function">nope₂</a> <a id="41696" class="Symbol">(</a><a id="41697" href="plfa.part2.Lambda.html#33645" class="InductiveConstructor">⊢ƛ</a> <a id="41700" class="Symbol">(</a><a id="41701" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="41704" href="plfa.part2.Lambda.html#41704" class="Bound">∋x</a> <a id="41707" href="plfa.part2.Lambda.html#33752" class="InductiveConstructor Operator">·</a> <a id="41709" href="plfa.part2.Lambda.html#33566" class="InductiveConstructor">⊢`</a> <a id="41712" href="plfa.part2.Lambda.html#41712" class="Bound">∋x′</a><a id="41715" class="Symbol">))</a>  <a id="41719" class="Symbol">=</a>  <a id="41722" href="plfa.part2.Lambda.html#41767" class="Function">contradiction</a> <a id="41736" class="Symbol">(</a><a id="41737" href="plfa.part2.Lambda.html#40687" class="Function">∋-injective</a> <a id="41749" href="plfa.part2.Lambda.html#41704" class="Bound">∋x</a> <a id="41752" href="plfa.part2.Lambda.html#41712" class="Bound">∋x′</a><a id="41755" class="Symbol">)</a>
  <a id="41759" class="Keyword">where</a>
  <a id="41767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41767" class="Function">contradiction</a> <a id="41781" class="Symbol">:</a> <a id="41783" class="Symbol">∀</a> <a id="41785" class="Symbol">{</a><a id="41786" href="plfa.part2.Lambda.html#41786" class="Bound">A</a> <a id="41788" href="plfa.part2.Lambda.html#41788" class="Bound">B</a><a id="41789" class="Symbol">}</a> <a id="41791" class="Symbol">→</a> <a id="41793" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41795" class="Symbol">(</a><a id="41796" href="plfa.part2.Lambda.html#41786" class="Bound">A</a> <a id="41798" href="plfa.part2.Lambda.html#29473" class="InductiveConstructor Operator">⇒</a> <a id="41800" href="plfa.part2.Lambda.html#41788" class="Bound">B</a> <a id="41802" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="41804" href="plfa.part2.Lambda.html#41786" class="Bound">A</a><a id="41805" class="Symbol">)</a>
  <a id="41809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41767" class="Function">contradiction</a> <a id="41823" class="Symbol">()</a>
</pre>{% endraw %}

#### Quiz

For each of the following, give a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A ``
2. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A ``
3. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A ``

For each of the following, give types `A`, `B`, and `C` for which it is derivable,
or explain why there are no such types.

1. `` ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B ``
2. `` ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C ``


#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42502" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ-type` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42673" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·  U+00B7  MIDDLE DOT (\cdot)
    —  U+2014  EM DASH (\em)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG or \Gamma)
    ≠  U+2260  NOT EQUAL TO (\=n or \ne)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ∅  U+2205  EMPTY SET (\0)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
    😇  U+1F607  SMILING FACE WITH HALO
    😈  U+1F608  SMILING FACE WITH HORNS

We compose reduction `—→` from an em dash `—` and an arrow `→`.
Similarly for reflexive and transitive closure `—↠`.
