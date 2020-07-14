---
src       : "src/plfa/Relations.lagda.md"
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

{% raw %}<pre class="Agda"><a id="161" class="Keyword">module</a> <a id="168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="183" class="Keyword">where</a>
</pre>{% endraw %}
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

{% raw %}<pre class="Agda"><a id="348" class="Keyword">import</a> <a id="355" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="393" class="Symbol">as</a> <a id="396" class="Module">Eq</a>
<a id="399" class="Keyword">open</a> <a id="404" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="407" class="Keyword">using</a> <a id="413" class="Symbol">(</a><a id="414" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="417" class="Symbol">;</a> <a id="419" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="423" class="Symbol">;</a> <a id="425" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="429" class="Symbol">)</a>
<a id="431" class="Keyword">open</a> <a id="436" class="Keyword">import</a> <a id="443" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="452" class="Keyword">using</a> <a id="458" class="Symbol">(</a><a id="459" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="460" class="Symbol">;</a> <a id="462" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="466" class="Symbol">;</a> <a id="468" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="471" class="Symbol">;</a> <a id="473" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="476" class="Symbol">)</a>
<a id="478" class="Keyword">open</a> <a id="483" class="Keyword">import</a> <a id="490" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="510" class="Keyword">using</a> <a id="516" class="Symbol">(</a><a id="517" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="523" class="Symbol">)</a>
</pre>{% endraw %}

## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
{% raw %}<pre class="Agda"><a id="1184" class="Keyword">data</a> <a id="_≤_"></a><a id="1189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1189" class="Datatype Operator">_≤_</a> <a id="1193" class="Symbol">:</a> <a id="1195" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1197" class="Symbol">→</a> <a id="1199" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1201" class="Symbol">→</a> <a id="1203" class="PrimitiveType">Set</a> <a id="1207" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1216" class="InductiveConstructor">z≤n</a> <a id="1220" class="Symbol">:</a> <a id="1222" class="Symbol">∀</a> <a id="1224" class="Symbol">{</a><a id="1225" href="plfa.Relations.html#1225" class="Bound">n</a> <a id="1227" class="Symbol">:</a> <a id="1229" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1230" class="Symbol">}</a>
      <a id="1238" class="Comment">--------</a>
    <a id="1251" class="Symbol">→</a> <a id="1253" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1189" class="Datatype Operator">≤</a> <a id="1260" href="plfa.Relations.html#1225" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="1269" class="Symbol">:</a> <a id="1271" class="Symbol">∀</a> <a id="1273" class="Symbol">{</a><a id="1274" href="plfa.Relations.html#1274" class="Bound">m</a> <a id="1276" href="plfa.Relations.html#1276" class="Bound">n</a> <a id="1278" class="Symbol">:</a> <a id="1280" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1281" class="Symbol">}</a>
    <a id="1287" class="Symbol">→</a> <a id="1289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1274" class="Bound">m</a> <a id="1291" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="1293" href="plfa.Relations.html#1276" class="Bound">n</a>
      <a id="1301" class="Comment">-------------</a>
    <a id="1319" class="Symbol">→</a> <a id="1321" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1274" class="Bound">m</a> <a id="1327" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="1329" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1333" href="plfa.Relations.html#1276" class="Bound">n</a>
</pre>{% endraw %}Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
{% raw %}<pre class="Agda"><a id="2595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2595" class="Function">_</a> <a id="2597" class="Symbol">:</a> <a id="2599" class="Number">2</a> <a id="2601" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="2603" class="Number">4</a>
<a id="2605" class="Symbol">_</a> <a id="2607" class="Symbol">=</a> <a id="2609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="2613" class="Symbol">(</a><a id="2614" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="2618" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a><a id="2621" class="Symbol">)</a>
</pre>{% endraw %}



## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
{% raw %}<pre class="Agda"><a id="3600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3600" class="Function">_</a> <a id="3602" class="Symbol">:</a> <a id="3604" class="Number">2</a> <a id="3606" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="3608" class="Number">4</a>
<a id="3610" class="Symbol">_</a> <a id="3612" class="Symbol">=</a> <a id="3614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="3618" class="Symbol">{</a><a id="3619" class="Number">1</a><a id="3620" class="Symbol">}</a> <a id="3622" class="Symbol">{</a><a id="3623" class="Number">3</a><a id="3624" class="Symbol">}</a> <a id="3626" class="Symbol">(</a><a id="3627" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="3631" class="Symbol">{</a><a id="3632" class="Number">0</a><a id="3633" class="Symbol">}</a> <a id="3635" class="Symbol">{</a><a id="3636" class="Number">2</a><a id="3637" class="Symbol">}</a> <a id="3639" class="Symbol">(</a><a id="3640" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a> <a id="3644" class="Symbol">{</a><a id="3645" class="Number">2</a><a id="3646" class="Symbol">}))</a>
</pre>{% endraw %}One may also identify implicit arguments by name:
{% raw %}<pre class="Agda"><a id="3708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3708" class="Function">_</a> <a id="3710" class="Symbol">:</a> <a id="3712" class="Number">2</a> <a id="3714" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="3716" class="Number">4</a>
<a id="3718" class="Symbol">_</a> <a id="3720" class="Symbol">=</a> <a id="3722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="3726" class="Symbol">{</a><a id="3727" class="Argument">m</a> <a id="3729" class="Symbol">=</a> <a id="3731" class="Number">1</a><a id="3732" class="Symbol">}</a> <a id="3734" class="Symbol">{</a><a id="3735" class="Argument">n</a> <a id="3737" class="Symbol">=</a> <a id="3739" class="Number">3</a><a id="3740" class="Symbol">}</a> <a id="3742" class="Symbol">(</a><a id="3743" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="3747" class="Symbol">{</a><a id="3748" class="Argument">m</a> <a id="3750" class="Symbol">=</a> <a id="3752" class="Number">0</a><a id="3753" class="Symbol">}</a> <a id="3755" class="Symbol">{</a><a id="3756" class="Argument">n</a> <a id="3758" class="Symbol">=</a> <a id="3760" class="Number">2</a><a id="3761" class="Symbol">}</a> <a id="3763" class="Symbol">(</a><a id="3764" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a> <a id="3768" class="Symbol">{</a><a id="3769" class="Argument">n</a> <a id="3771" class="Symbol">=</a> <a id="3773" class="Number">2</a><a id="3774" class="Symbol">}))</a>
</pre>{% endraw %}In the latter format, you may only supply some implicit arguments:
{% raw %}<pre class="Agda"><a id="3853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3853" class="Function">_</a> <a id="3855" class="Symbol">:</a> <a id="3857" class="Number">2</a> <a id="3859" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="3861" class="Number">4</a>
<a id="3863" class="Symbol">_</a> <a id="3865" class="Symbol">=</a> <a id="3867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="3871" class="Symbol">{</a><a id="3872" class="Argument">n</a> <a id="3874" class="Symbol">=</a> <a id="3876" class="Number">3</a><a id="3877" class="Symbol">}</a> <a id="3879" class="Symbol">(</a><a id="3880" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="3884" class="Symbol">{</a><a id="3885" class="Argument">n</a> <a id="3887" class="Symbol">=</a> <a id="3889" class="Number">2</a><a id="3890" class="Symbol">}</a> <a id="3892" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a><a id="3895" class="Symbol">)</a>
</pre>{% endraw %}It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows:
{% raw %}<pre class="Agda"><a id="4040" class="Keyword">infix</a> <a id="4046" class="Number">4</a> <a id="4048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1189" class="Datatype Operator">_≤_</a>
</pre>{% endraw %}We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}/Decidable/).


## Inversion

In our defintions, we go from smaller things to larger things.
For instance, form `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
{% raw %}<pre class="Agda"><a id="inv-s≤s"></a><a id="5065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5065" class="Function">inv-s≤s</a> <a id="5073" class="Symbol">:</a> <a id="5075" class="Symbol">∀</a> <a id="5077" class="Symbol">{</a><a id="5078" href="plfa.Relations.html#5078" class="Bound">m</a> <a id="5080" href="plfa.Relations.html#5080" class="Bound">n</a> <a id="5082" class="Symbol">:</a> <a id="5084" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5085" class="Symbol">}</a>
  <a id="5089" class="Symbol">→</a> <a id="5091" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5078" class="Bound">m</a> <a id="5097" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="5099" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5103" href="plfa.Relations.html#5080" class="Bound">n</a>
    <a id="5109" class="Comment">-------------</a>
  <a id="5125" class="Symbol">→</a> <a id="5127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5078" class="Bound">m</a> <a id="5129" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="5131" href="plfa.Relations.html#5080" class="Bound">n</a>
<a id="5133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5065" class="Function">inv-s≤s</a> <a id="5141" class="Symbol">(</a><a id="5142" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="5146" href="plfa.Relations.html#5146" class="Bound">m≤n</a><a id="5149" class="Symbol">)</a> <a id="5151" class="Symbol">=</a> <a id="5153" href="plfa.Relations.html#5146" class="Bound">m≤n</a>
</pre>{% endraw %}Here `m≤n` (with no spaces) is a variable name while
`m ≤ n` (with spaces) is a type, and the latter
is the type of the former.  It is a common convention
in Agda to choose derive a variable name by removing
spaces from its type.

Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
{% raw %}<pre class="Agda"><a id="inv-z≤n"></a><a id="5668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5668" class="Function">inv-z≤n</a> <a id="5676" class="Symbol">:</a> <a id="5678" class="Symbol">∀</a> <a id="5680" class="Symbol">{</a><a id="5681" href="plfa.Relations.html#5681" class="Bound">m</a> <a id="5683" class="Symbol">:</a> <a id="5685" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5686" class="Symbol">}</a>
  <a id="5690" class="Symbol">→</a> <a id="5692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5681" class="Bound">m</a> <a id="5694" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="5696" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
    <a id="5705" class="Comment">--------</a>
  <a id="5716" class="Symbol">→</a> <a id="5718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5681" class="Bound">m</a> <a id="5720" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5722" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
<a id="5727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5668" class="Function">inv-z≤n</a> <a id="5735" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a> <a id="5739" class="Symbol">=</a> <a id="5741" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

{% raw %}<pre class="Agda"><a id="7232" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
Give an example of a partial order that is not a total order.

{% raw %}<pre class="Agda"><a id="7327" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{% raw %}<pre class="Agda"><a id="≤-refl"></a><a id="7627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7627" class="Function">≤-refl</a> <a id="7634" class="Symbol">:</a> <a id="7636" class="Symbol">∀</a> <a id="7638" class="Symbol">{</a><a id="7639" href="plfa.Relations.html#7639" class="Bound">n</a> <a id="7641" class="Symbol">:</a> <a id="7643" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7644" class="Symbol">}</a>
    <a id="7650" class="Comment">-----</a>
  <a id="7658" class="Symbol">→</a> <a id="7660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7639" class="Bound">n</a> <a id="7662" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="7664" href="plfa.Relations.html#7639" class="Bound">n</a>
<a id="7666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7627" class="Function">≤-refl</a> <a id="7673" class="Symbol">{</a><a id="7674" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="7678" class="Symbol">}</a> <a id="7680" class="Symbol">=</a> <a id="7682" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="7686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7627" class="Function">≤-refl</a> <a id="7693" class="Symbol">{</a><a id="7694" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7698" href="plfa.Relations.html#7698" class="Bound">n</a><a id="7699" class="Symbol">}</a> <a id="7701" class="Symbol">=</a> <a id="7703" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="7707" href="plfa.Relations.html#7627" class="Function">≤-refl</a>
</pre>{% endraw %}The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
{% raw %}<pre class="Agda"><a id="≤-trans"></a><a id="8344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8344" class="Function">≤-trans</a> <a id="8352" class="Symbol">:</a> <a id="8354" class="Symbol">∀</a> <a id="8356" class="Symbol">{</a><a id="8357" href="plfa.Relations.html#8357" class="Bound">m</a> <a id="8359" href="plfa.Relations.html#8359" class="Bound">n</a> <a id="8361" href="plfa.Relations.html#8361" class="Bound">p</a> <a id="8363" class="Symbol">:</a> <a id="8365" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8366" class="Symbol">}</a>
  <a id="8370" class="Symbol">→</a> <a id="8372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8357" class="Bound">m</a> <a id="8374" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="8376" href="plfa.Relations.html#8359" class="Bound">n</a>
  <a id="8380" class="Symbol">→</a> <a id="8382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8359" class="Bound">n</a> <a id="8384" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="8386" href="plfa.Relations.html#8361" class="Bound">p</a>
    <a id="8392" class="Comment">-----</a>
  <a id="8400" class="Symbol">→</a> <a id="8402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8357" class="Bound">m</a> <a id="8404" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="8406" href="plfa.Relations.html#8361" class="Bound">p</a>
<a id="8408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8344" class="Function">≤-trans</a> <a id="8416" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>       <a id="8426" class="Symbol">_</a>          <a id="8437" class="Symbol">=</a>  <a id="8440" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="8444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8344" class="Function">≤-trans</a> <a id="8452" class="Symbol">(</a><a id="8453" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="8457" href="plfa.Relations.html#8457" class="Bound">m≤n</a><a id="8460" class="Symbol">)</a> <a id="8462" class="Symbol">(</a><a id="8463" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="8467" href="plfa.Relations.html#8467" class="Bound">n≤p</a><a id="8470" class="Symbol">)</a>  <a id="8473" class="Symbol">=</a>  <a id="8476" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="8480" class="Symbol">(</a><a id="8481" href="plfa.Relations.html#8344" class="Function">≤-trans</a> <a id="8489" href="plfa.Relations.html#8457" class="Bound">m≤n</a> <a id="8493" href="plfa.Relations.html#8467" class="Bound">n≤p</a><a id="8496" class="Symbol">)</a>
</pre>{% endraw %}Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
{% raw %}<pre class="Agda"><a id="≤-trans′"></a><a id="9457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9457" class="Function">≤-trans′</a> <a id="9466" class="Symbol">:</a> <a id="9468" class="Symbol">∀</a> <a id="9470" class="Symbol">(</a><a id="9471" href="plfa.Relations.html#9471" class="Bound">m</a> <a id="9473" href="plfa.Relations.html#9473" class="Bound">n</a> <a id="9475" href="plfa.Relations.html#9475" class="Bound">p</a> <a id="9477" class="Symbol">:</a> <a id="9479" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9480" class="Symbol">)</a>
  <a id="9484" class="Symbol">→</a> <a id="9486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9471" class="Bound">m</a> <a id="9488" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="9490" href="plfa.Relations.html#9473" class="Bound">n</a>
  <a id="9494" class="Symbol">→</a> <a id="9496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9473" class="Bound">n</a> <a id="9498" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="9500" href="plfa.Relations.html#9475" class="Bound">p</a>
    <a id="9506" class="Comment">-----</a>
  <a id="9514" class="Symbol">→</a> <a id="9516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9471" class="Bound">m</a> <a id="9518" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="9520" href="plfa.Relations.html#9475" class="Bound">p</a>
<a id="9522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9457" class="Function">≤-trans′</a> <a id="9531" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="9539" class="Symbol">_</a>       <a id="9547" class="Symbol">_</a>       <a id="9555" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>       <a id="9565" class="Symbol">_</a>          <a id="9576" class="Symbol">=</a>  <a id="9579" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="9583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9457" class="Function">≤-trans′</a> <a id="9592" class="Symbol">(</a><a id="9593" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9597" href="plfa.Relations.html#9597" class="Bound">m</a><a id="9598" class="Symbol">)</a> <a id="9600" class="Symbol">(</a><a id="9601" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9605" href="plfa.Relations.html#9605" class="Bound">n</a><a id="9606" class="Symbol">)</a> <a id="9608" class="Symbol">(</a><a id="9609" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9613" href="plfa.Relations.html#9613" class="Bound">p</a><a id="9614" class="Symbol">)</a> <a id="9616" class="Symbol">(</a><a id="9617" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="9621" href="plfa.Relations.html#9621" class="Bound">m≤n</a><a id="9624" class="Symbol">)</a> <a id="9626" class="Symbol">(</a><a id="9627" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="9631" href="plfa.Relations.html#9631" class="Bound">n≤p</a><a id="9634" class="Symbol">)</a>  <a id="9637" class="Symbol">=</a>  <a id="9640" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="9644" class="Symbol">(</a><a id="9645" href="plfa.Relations.html#9457" class="Function">≤-trans′</a> <a id="9654" href="plfa.Relations.html#9597" class="Bound">m</a> <a id="9656" href="plfa.Relations.html#9605" class="Bound">n</a> <a id="9658" href="plfa.Relations.html#9613" class="Bound">p</a> <a id="9660" href="plfa.Relations.html#9621" class="Bound">m≤n</a> <a id="9664" href="plfa.Relations.html#9631" class="Bound">n≤p</a><a id="9667" class="Symbol">)</a>
</pre>{% endraw %}One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
{% raw %}<pre class="Agda"><a id="≤-antisym"></a><a id="10412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10412" class="Function">≤-antisym</a> <a id="10422" class="Symbol">:</a> <a id="10424" class="Symbol">∀</a> <a id="10426" class="Symbol">{</a><a id="10427" href="plfa.Relations.html#10427" class="Bound">m</a> <a id="10429" href="plfa.Relations.html#10429" class="Bound">n</a> <a id="10431" class="Symbol">:</a> <a id="10433" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10434" class="Symbol">}</a>
  <a id="10438" class="Symbol">→</a> <a id="10440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10427" class="Bound">m</a> <a id="10442" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="10444" href="plfa.Relations.html#10429" class="Bound">n</a>
  <a id="10448" class="Symbol">→</a> <a id="10450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10429" class="Bound">n</a> <a id="10452" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="10454" href="plfa.Relations.html#10427" class="Bound">m</a>
    <a id="10460" class="Comment">-----</a>
  <a id="10468" class="Symbol">→</a> <a id="10470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10427" class="Bound">m</a> <a id="10472" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10474" href="plfa.Relations.html#10429" class="Bound">n</a>
<a id="10476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10412" class="Function">≤-antisym</a> <a id="10486" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>       <a id="10496" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>        <a id="10507" class="Symbol">=</a>  <a id="10510" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="10515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10412" class="Function">≤-antisym</a> <a id="10525" class="Symbol">(</a><a id="10526" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="10530" href="plfa.Relations.html#10530" class="Bound">m≤n</a><a id="10533" class="Symbol">)</a> <a id="10535" class="Symbol">(</a><a id="10536" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="10540" href="plfa.Relations.html#10540" class="Bound">n≤m</a><a id="10543" class="Symbol">)</a>  <a id="10546" class="Symbol">=</a>  <a id="10549" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="10554" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10558" class="Symbol">(</a><a id="10559" href="plfa.Relations.html#10412" class="Function">≤-antisym</a> <a id="10569" href="plfa.Relations.html#10530" class="Bound">m≤n</a> <a id="10573" href="plfa.Relations.html#10540" class="Bound">n≤m</a><a id="10576" class="Symbol">)</a>
</pre>{% endraw %}Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

{% raw %}<pre class="Agda"><a id="11371" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
{% raw %}<pre class="Agda"><a id="11625" class="Keyword">data</a> <a id="Total"></a><a id="11630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11630" class="Datatype">Total</a> <a id="11636" class="Symbol">(</a><a id="11637" href="plfa.Relations.html#11637" class="Bound">m</a> <a id="11639" href="plfa.Relations.html#11639" class="Bound">n</a> <a id="11641" class="Symbol">:</a> <a id="11643" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11644" class="Symbol">)</a> <a id="11646" class="Symbol">:</a> <a id="11648" class="PrimitiveType">Set</a> <a id="11652" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="11661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11661" class="InductiveConstructor">forward</a> <a id="11669" class="Symbol">:</a>
      <a id="11677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11637" class="Bound">m</a> <a id="11679" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="11681" href="plfa.Relations.html#11639" class="Bound">n</a>
      <a id="11689" class="Comment">---------</a>
    <a id="11703" class="Symbol">→</a> <a id="11705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11630" class="Datatype">Total</a> <a id="11711" href="plfa.Relations.html#11637" class="Bound">m</a> <a id="11713" href="plfa.Relations.html#11639" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="11718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11718" class="InductiveConstructor">flipped</a> <a id="11726" class="Symbol">:</a>
      <a id="11734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11639" class="Bound">n</a> <a id="11736" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="11738" href="plfa.Relations.html#11637" class="Bound">m</a>
      <a id="11746" class="Comment">---------</a>
    <a id="11760" class="Symbol">→</a> <a id="11762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11630" class="Datatype">Total</a> <a id="11768" href="plfa.Relations.html#11637" class="Bound">m</a> <a id="11770" href="plfa.Relations.html#11639" class="Bound">n</a>
</pre>{% endraw %}Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}/Connectives/).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{% raw %}<pre class="Agda"><a id="12259" class="Keyword">data</a> <a id="Total′"></a><a id="12264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12264" class="Datatype">Total′</a> <a id="12271" class="Symbol">:</a> <a id="12273" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12275" class="Symbol">→</a> <a id="12277" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12279" class="Symbol">→</a> <a id="12281" class="PrimitiveType">Set</a> <a id="12285" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="12294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12294" class="InductiveConstructor">forward′</a> <a id="12303" class="Symbol">:</a> <a id="12305" class="Symbol">∀</a> <a id="12307" class="Symbol">{</a><a id="12308" href="plfa.Relations.html#12308" class="Bound">m</a> <a id="12310" href="plfa.Relations.html#12310" class="Bound">n</a> <a id="12312" class="Symbol">:</a> <a id="12314" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12315" class="Symbol">}</a>
    <a id="12321" class="Symbol">→</a> <a id="12323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12308" class="Bound">m</a> <a id="12325" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="12327" href="plfa.Relations.html#12310" class="Bound">n</a>
      <a id="12335" class="Comment">----------</a>
    <a id="12350" class="Symbol">→</a> <a id="12352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12264" class="Datatype">Total′</a> <a id="12359" href="plfa.Relations.html#12308" class="Bound">m</a> <a id="12361" href="plfa.Relations.html#12310" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="12366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12366" class="InductiveConstructor">flipped′</a> <a id="12375" class="Symbol">:</a> <a id="12377" class="Symbol">∀</a> <a id="12379" class="Symbol">{</a><a id="12380" href="plfa.Relations.html#12380" class="Bound">m</a> <a id="12382" href="plfa.Relations.html#12382" class="Bound">n</a> <a id="12384" class="Symbol">:</a> <a id="12386" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12387" class="Symbol">}</a>
    <a id="12393" class="Symbol">→</a> <a id="12395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12382" class="Bound">n</a> <a id="12397" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="12399" href="plfa.Relations.html#12380" class="Bound">m</a>
      <a id="12407" class="Comment">----------</a>
    <a id="12422" class="Symbol">→</a> <a id="12424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12264" class="Datatype">Total′</a> <a id="12431" href="plfa.Relations.html#12380" class="Bound">m</a> <a id="12433" href="plfa.Relations.html#12382" class="Bound">n</a>
</pre>{% endraw %}Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
{% raw %}<pre class="Agda"><a id="≤-total"></a><a id="12952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12952" class="Function">≤-total</a> <a id="12960" class="Symbol">:</a> <a id="12962" class="Symbol">∀</a> <a id="12964" class="Symbol">(</a><a id="12965" href="plfa.Relations.html#12965" class="Bound">m</a> <a id="12967" href="plfa.Relations.html#12967" class="Bound">n</a> <a id="12969" class="Symbol">:</a> <a id="12971" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12972" class="Symbol">)</a> <a id="12974" class="Symbol">→</a> <a id="12976" href="plfa.Relations.html#11630" class="Datatype">Total</a> <a id="12982" href="plfa.Relations.html#12965" class="Bound">m</a> <a id="12984" href="plfa.Relations.html#12967" class="Bound">n</a>
<a id="12986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12952" class="Function">≤-total</a> <a id="12994" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="13002" href="plfa.Relations.html#13002" class="Bound">n</a>                         <a id="13028" class="Symbol">=</a>  <a id="13031" href="plfa.Relations.html#11661" class="InductiveConstructor">forward</a> <a id="13039" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="13043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12952" class="Function">≤-total</a> <a id="13051" class="Symbol">(</a><a id="13052" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13056" href="plfa.Relations.html#13056" class="Bound">m</a><a id="13057" class="Symbol">)</a> <a id="13059" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="13085" class="Symbol">=</a>  <a id="13088" href="plfa.Relations.html#11718" class="InductiveConstructor">flipped</a> <a id="13096" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="13100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12952" class="Function">≤-total</a> <a id="13108" class="Symbol">(</a><a id="13109" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13113" href="plfa.Relations.html#13113" class="Bound">m</a><a id="13114" class="Symbol">)</a> <a id="13116" class="Symbol">(</a><a id="13117" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13121" href="plfa.Relations.html#13121" class="Bound">n</a><a id="13122" class="Symbol">)</a> <a id="13124" class="Keyword">with</a> <a id="13129" href="plfa.Relations.html#12952" class="Function">≤-total</a> <a id="13137" href="plfa.Relations.html#13113" class="Bound">m</a> <a id="13139" href="plfa.Relations.html#13121" class="Bound">n</a>
<a id="13141" class="Symbol">...</a>                        <a id="13168" class="Symbol">|</a> <a id="13170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11661" class="InductiveConstructor">forward</a> <a id="13178" href="plfa.Relations.html#13178" class="Bound">m≤n</a>  <a id="13183" class="Symbol">=</a>  <a id="13186" href="plfa.Relations.html#11661" class="InductiveConstructor">forward</a> <a id="13194" class="Symbol">(</a><a id="13195" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="13199" href="plfa.Relations.html#13178" class="Bound">m≤n</a><a id="13202" class="Symbol">)</a>
<a id="13204" class="Symbol">...</a>                        <a id="13231" class="Symbol">|</a> <a id="13233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11718" class="InductiveConstructor">flipped</a> <a id="13241" href="plfa.Relations.html#13241" class="Bound">n≤m</a>  <a id="13246" class="Symbol">=</a>  <a id="13249" href="plfa.Relations.html#11718" class="InductiveConstructor">flipped</a> <a id="13257" class="Symbol">(</a><a id="13258" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="13262" href="plfa.Relations.html#13241" class="Bound">n≤m</a><a id="13265" class="Symbol">)</a>
</pre>{% endraw %}In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
{% raw %}<pre class="Agda"><a id="≤-total′"></a><a id="14757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14757" class="Function">≤-total′</a> <a id="14766" class="Symbol">:</a> <a id="14768" class="Symbol">∀</a> <a id="14770" class="Symbol">(</a><a id="14771" href="plfa.Relations.html#14771" class="Bound">m</a> <a id="14773" href="plfa.Relations.html#14773" class="Bound">n</a> <a id="14775" class="Symbol">:</a> <a id="14777" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14778" class="Symbol">)</a> <a id="14780" class="Symbol">→</a> <a id="14782" href="plfa.Relations.html#11630" class="Datatype">Total</a> <a id="14788" href="plfa.Relations.html#14771" class="Bound">m</a> <a id="14790" href="plfa.Relations.html#14773" class="Bound">n</a>
<a id="14792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14757" class="Function">≤-total′</a> <a id="14801" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="14809" href="plfa.Relations.html#14809" class="Bound">n</a>        <a id="14818" class="Symbol">=</a>  <a id="14821" href="plfa.Relations.html#11661" class="InductiveConstructor">forward</a> <a id="14829" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="14833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14757" class="Function">≤-total′</a> <a id="14842" class="Symbol">(</a><a id="14843" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14847" href="plfa.Relations.html#14847" class="Bound">m</a><a id="14848" class="Symbol">)</a> <a id="14850" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="14859" class="Symbol">=</a>  <a id="14862" href="plfa.Relations.html#11718" class="InductiveConstructor">flipped</a> <a id="14870" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="14874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14757" class="Function">≤-total′</a> <a id="14883" class="Symbol">(</a><a id="14884" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14888" href="plfa.Relations.html#14888" class="Bound">m</a><a id="14889" class="Symbol">)</a> <a id="14891" class="Symbol">(</a><a id="14892" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14896" href="plfa.Relations.html#14896" class="Bound">n</a><a id="14897" class="Symbol">)</a>  <a id="14900" class="Symbol">=</a>  <a id="14903" href="plfa.Relations.html#14935" class="Function">helper</a> <a id="14910" class="Symbol">(</a><a id="14911" href="plfa.Relations.html#14757" class="Function">≤-total′</a> <a id="14920" href="plfa.Relations.html#14888" class="Bound">m</a> <a id="14922" href="plfa.Relations.html#14896" class="Bound">n</a><a id="14923" class="Symbol">)</a>
  <a id="14927" class="Keyword">where</a>
  <a id="14935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14935" class="Function">helper</a> <a id="14942" class="Symbol">:</a> <a id="14944" href="plfa.Relations.html#11630" class="Datatype">Total</a> <a id="14950" href="plfa.Relations.html#14888" class="Bound">m</a> <a id="14952" href="plfa.Relations.html#14896" class="Bound">n</a> <a id="14954" class="Symbol">→</a> <a id="14956" href="plfa.Relations.html#11630" class="Datatype">Total</a> <a id="14962" class="Symbol">(</a><a id="14963" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14967" href="plfa.Relations.html#14888" class="Bound">m</a><a id="14968" class="Symbol">)</a> <a id="14970" class="Symbol">(</a><a id="14971" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14975" href="plfa.Relations.html#14896" class="Bound">n</a><a id="14976" class="Symbol">)</a>
  <a id="14980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14935" class="Function">helper</a> <a id="14987" class="Symbol">(</a><a id="14988" href="plfa.Relations.html#11661" class="InductiveConstructor">forward</a> <a id="14996" href="plfa.Relations.html#14996" class="Bound">m≤n</a><a id="14999" class="Symbol">)</a>  <a id="15002" class="Symbol">=</a>  <a id="15005" href="plfa.Relations.html#11661" class="InductiveConstructor">forward</a> <a id="15013" class="Symbol">(</a><a id="15014" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="15018" href="plfa.Relations.html#14996" class="Bound">m≤n</a><a id="15021" class="Symbol">)</a>
  <a id="15025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14935" class="Function">helper</a> <a id="15032" class="Symbol">(</a><a id="15033" href="plfa.Relations.html#11718" class="InductiveConstructor">flipped</a> <a id="15041" href="plfa.Relations.html#15041" class="Bound">n≤m</a><a id="15044" class="Symbol">)</a>  <a id="15047" class="Symbol">=</a>  <a id="15050" href="plfa.Relations.html#11718" class="InductiveConstructor">flipped</a> <a id="15058" class="Symbol">(</a><a id="15059" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="15063" href="plfa.Relations.html#15041" class="Bound">n≤m</a><a id="15066" class="Symbol">)</a>
</pre>{% endraw %}This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{% raw %}<pre class="Agda"><a id="≤-total″"></a><a id="15688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15688" class="Function">≤-total″</a> <a id="15697" class="Symbol">:</a> <a id="15699" class="Symbol">∀</a> <a id="15701" class="Symbol">(</a><a id="15702" href="plfa.Relations.html#15702" class="Bound">m</a> <a id="15704" href="plfa.Relations.html#15704" class="Bound">n</a> <a id="15706" class="Symbol">:</a> <a id="15708" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15709" class="Symbol">)</a> <a id="15711" class="Symbol">→</a> <a id="15713" href="plfa.Relations.html#11630" class="Datatype">Total</a> <a id="15719" href="plfa.Relations.html#15702" class="Bound">m</a> <a id="15721" href="plfa.Relations.html#15704" class="Bound">n</a>
<a id="15723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15688" class="Function">≤-total″</a> <a id="15732" href="plfa.Relations.html#15732" class="Bound">m</a>       <a id="15740" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="15766" class="Symbol">=</a>  <a id="15769" href="plfa.Relations.html#11718" class="InductiveConstructor">flipped</a> <a id="15777" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="15781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15688" class="Function">≤-total″</a> <a id="15790" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="15798" class="Symbol">(</a><a id="15799" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15803" href="plfa.Relations.html#15803" class="Bound">n</a><a id="15804" class="Symbol">)</a>                   <a id="15824" class="Symbol">=</a>  <a id="15827" href="plfa.Relations.html#11661" class="InductiveConstructor">forward</a> <a id="15835" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="15839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15688" class="Function">≤-total″</a> <a id="15848" class="Symbol">(</a><a id="15849" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15853" href="plfa.Relations.html#15853" class="Bound">m</a><a id="15854" class="Symbol">)</a> <a id="15856" class="Symbol">(</a><a id="15857" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15861" href="plfa.Relations.html#15861" class="Bound">n</a><a id="15862" class="Symbol">)</a> <a id="15864" class="Keyword">with</a> <a id="15869" href="plfa.Relations.html#15688" class="Function">≤-total″</a> <a id="15878" href="plfa.Relations.html#15853" class="Bound">m</a> <a id="15880" href="plfa.Relations.html#15861" class="Bound">n</a>
<a id="15882" class="Symbol">...</a>                        <a id="15909" class="Symbol">|</a> <a id="15911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11661" class="InductiveConstructor">forward</a> <a id="15919" href="plfa.Relations.html#15919" class="Bound">m≤n</a>   <a id="15925" class="Symbol">=</a>  <a id="15928" href="plfa.Relations.html#11661" class="InductiveConstructor">forward</a> <a id="15936" class="Symbol">(</a><a id="15937" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="15941" href="plfa.Relations.html#15919" class="Bound">m≤n</a><a id="15944" class="Symbol">)</a>
<a id="15946" class="Symbol">...</a>                        <a id="15973" class="Symbol">|</a> <a id="15975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11718" class="InductiveConstructor">flipped</a> <a id="15983" href="plfa.Relations.html#15983" class="Bound">n≤m</a>   <a id="15989" class="Symbol">=</a>  <a id="15992" href="plfa.Relations.html#11718" class="InductiveConstructor">flipped</a> <a id="16000" class="Symbol">(</a><a id="16001" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="16005" href="plfa.Relations.html#15983" class="Bound">n≤m</a><a id="16008" class="Symbol">)</a>
</pre>{% endraw %}It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
{% raw %}<pre class="Agda"><a id="+-monoʳ-≤"></a><a id="16597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16597" class="Function">+-monoʳ-≤</a> <a id="16607" class="Symbol">:</a> <a id="16609" class="Symbol">∀</a> <a id="16611" class="Symbol">(</a><a id="16612" href="plfa.Relations.html#16612" class="Bound">n</a> <a id="16614" href="plfa.Relations.html#16614" class="Bound">p</a> <a id="16616" href="plfa.Relations.html#16616" class="Bound">q</a> <a id="16618" class="Symbol">:</a> <a id="16620" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16621" class="Symbol">)</a>
  <a id="16625" class="Symbol">→</a> <a id="16627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16614" class="Bound">p</a> <a id="16629" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="16631" href="plfa.Relations.html#16616" class="Bound">q</a>
    <a id="16637" class="Comment">-------------</a>
  <a id="16653" class="Symbol">→</a> <a id="16655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16612" class="Bound">n</a> <a id="16657" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16659" href="plfa.Relations.html#16614" class="Bound">p</a> <a id="16661" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="16663" href="plfa.Relations.html#16612" class="Bound">n</a> <a id="16665" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16667" href="plfa.Relations.html#16616" class="Bound">q</a>
<a id="16669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16597" class="Function">+-monoʳ-≤</a> <a id="16679" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="16687" href="plfa.Relations.html#16687" class="Bound">p</a> <a id="16689" href="plfa.Relations.html#16689" class="Bound">q</a> <a id="16691" href="plfa.Relations.html#16691" class="Bound">p≤q</a>  <a id="16696" class="Symbol">=</a>  <a id="16699" href="plfa.Relations.html#16691" class="Bound">p≤q</a>
<a id="16703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16597" class="Function">+-monoʳ-≤</a> <a id="16713" class="Symbol">(</a><a id="16714" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16718" href="plfa.Relations.html#16718" class="Bound">n</a><a id="16719" class="Symbol">)</a> <a id="16721" href="plfa.Relations.html#16721" class="Bound">p</a> <a id="16723" href="plfa.Relations.html#16723" class="Bound">q</a> <a id="16725" href="plfa.Relations.html#16725" class="Bound">p≤q</a>  <a id="16730" class="Symbol">=</a>  <a id="16733" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="16737" class="Symbol">(</a><a id="16738" href="plfa.Relations.html#16597" class="Function">+-monoʳ-≤</a> <a id="16748" href="plfa.Relations.html#16718" class="Bound">n</a> <a id="16750" href="plfa.Relations.html#16721" class="Bound">p</a> <a id="16752" href="plfa.Relations.html#16723" class="Bound">q</a> <a id="16754" href="plfa.Relations.html#16725" class="Bound">p≤q</a><a id="16757" class="Symbol">)</a>
</pre>{% endraw %}The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
{% raw %}<pre class="Agda"><a id="+-monoˡ-≤"></a><a id="17397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17397" class="Function">+-monoˡ-≤</a> <a id="17407" class="Symbol">:</a> <a id="17409" class="Symbol">∀</a> <a id="17411" class="Symbol">(</a><a id="17412" href="plfa.Relations.html#17412" class="Bound">m</a> <a id="17414" href="plfa.Relations.html#17414" class="Bound">n</a> <a id="17416" href="plfa.Relations.html#17416" class="Bound">p</a> <a id="17418" class="Symbol">:</a> <a id="17420" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17421" class="Symbol">)</a>
  <a id="17425" class="Symbol">→</a> <a id="17427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17412" class="Bound">m</a> <a id="17429" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17431" href="plfa.Relations.html#17414" class="Bound">n</a>
    <a id="17437" class="Comment">-------------</a>
  <a id="17453" class="Symbol">→</a> <a id="17455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17412" class="Bound">m</a> <a id="17457" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17459" href="plfa.Relations.html#17416" class="Bound">p</a> <a id="17461" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17463" href="plfa.Relations.html#17414" class="Bound">n</a> <a id="17465" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17467" href="plfa.Relations.html#17416" class="Bound">p</a>
<a id="17469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17397" class="Function">+-monoˡ-≤</a> <a id="17479" href="plfa.Relations.html#17479" class="Bound">m</a> <a id="17481" href="plfa.Relations.html#17481" class="Bound">n</a> <a id="17483" href="plfa.Relations.html#17483" class="Bound">p</a> <a id="17485" href="plfa.Relations.html#17485" class="Bound">m≤n</a>  <a id="17490" class="Keyword">rewrite</a> <a id="17498" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17505" href="plfa.Relations.html#17479" class="Bound">m</a> <a id="17507" href="plfa.Relations.html#17483" class="Bound">p</a> <a id="17509" class="Symbol">|</a> <a id="17511" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17518" href="plfa.Relations.html#17481" class="Bound">n</a> <a id="17520" href="plfa.Relations.html#17483" class="Bound">p</a>  <a id="17523" class="Symbol">=</a> <a id="17525" href="plfa.Relations.html#16597" class="Function">+-monoʳ-≤</a> <a id="17535" href="plfa.Relations.html#17483" class="Bound">p</a> <a id="17537" href="plfa.Relations.html#17479" class="Bound">m</a> <a id="17539" href="plfa.Relations.html#17481" class="Bound">n</a> <a id="17541" href="plfa.Relations.html#17485" class="Bound">m≤n</a>
</pre>{% endraw %}Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
{% raw %}<pre class="Agda"><a id="+-mono-≤"></a><a id="17739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17739" class="Function">+-mono-≤</a> <a id="17748" class="Symbol">:</a> <a id="17750" class="Symbol">∀</a> <a id="17752" class="Symbol">(</a><a id="17753" href="plfa.Relations.html#17753" class="Bound">m</a> <a id="17755" href="plfa.Relations.html#17755" class="Bound">n</a> <a id="17757" href="plfa.Relations.html#17757" class="Bound">p</a> <a id="17759" href="plfa.Relations.html#17759" class="Bound">q</a> <a id="17761" class="Symbol">:</a> <a id="17763" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17764" class="Symbol">)</a>
  <a id="17768" class="Symbol">→</a> <a id="17770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17753" class="Bound">m</a> <a id="17772" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17774" href="plfa.Relations.html#17755" class="Bound">n</a>
  <a id="17778" class="Symbol">→</a> <a id="17780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17757" class="Bound">p</a> <a id="17782" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17784" href="plfa.Relations.html#17759" class="Bound">q</a>
    <a id="17790" class="Comment">-------------</a>
  <a id="17806" class="Symbol">→</a> <a id="17808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17753" class="Bound">m</a> <a id="17810" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17812" href="plfa.Relations.html#17757" class="Bound">p</a> <a id="17814" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17816" href="plfa.Relations.html#17755" class="Bound">n</a> <a id="17818" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17820" href="plfa.Relations.html#17759" class="Bound">q</a>
<a id="17822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17739" class="Function">+-mono-≤</a> <a id="17831" href="plfa.Relations.html#17831" class="Bound">m</a> <a id="17833" href="plfa.Relations.html#17833" class="Bound">n</a> <a id="17835" href="plfa.Relations.html#17835" class="Bound">p</a> <a id="17837" href="plfa.Relations.html#17837" class="Bound">q</a> <a id="17839" href="plfa.Relations.html#17839" class="Bound">m≤n</a> <a id="17843" href="plfa.Relations.html#17843" class="Bound">p≤q</a>  <a id="17848" class="Symbol">=</a>  <a id="17851" href="plfa.Relations.html#8344" class="Function">≤-trans</a> <a id="17859" class="Symbol">(</a><a id="17860" href="plfa.Relations.html#17397" class="Function">+-monoˡ-≤</a> <a id="17870" href="plfa.Relations.html#17831" class="Bound">m</a> <a id="17872" href="plfa.Relations.html#17833" class="Bound">n</a> <a id="17874" href="plfa.Relations.html#17835" class="Bound">p</a> <a id="17876" href="plfa.Relations.html#17839" class="Bound">m≤n</a><a id="17879" class="Symbol">)</a> <a id="17881" class="Symbol">(</a><a id="17882" href="plfa.Relations.html#16597" class="Function">+-monoʳ-≤</a> <a id="17892" href="plfa.Relations.html#17833" class="Bound">n</a> <a id="17894" href="plfa.Relations.html#17835" class="Bound">p</a> <a id="17896" href="plfa.Relations.html#17837" class="Bound">q</a> <a id="17898" href="plfa.Relations.html#17843" class="Bound">p≤q</a><a id="17901" class="Symbol">)</a>
</pre>{% endraw %}Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

{% raw %}<pre class="Agda"><a id="18210" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
{% raw %}<pre class="Agda"><a id="18343" class="Keyword">infix</a> <a id="18349" class="Number">4</a> <a id="18351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18361" class="Datatype Operator">_&lt;_</a>

<a id="18356" class="Keyword">data</a> <a id="_&lt;_"></a><a id="18361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18361" class="Datatype Operator">_&lt;_</a> <a id="18365" class="Symbol">:</a> <a id="18367" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18369" class="Symbol">→</a> <a id="18371" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18373" class="Symbol">→</a> <a id="18375" class="PrimitiveType">Set</a> <a id="18379" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="18388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18388" class="InductiveConstructor">z&lt;s</a> <a id="18392" class="Symbol">:</a> <a id="18394" class="Symbol">∀</a> <a id="18396" class="Symbol">{</a><a id="18397" href="plfa.Relations.html#18397" class="Bound">n</a> <a id="18399" class="Symbol">:</a> <a id="18401" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18402" class="Symbol">}</a>
      <a id="18410" class="Comment">------------</a>
    <a id="18427" class="Symbol">→</a> <a id="18429" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18361" class="Datatype Operator">&lt;</a> <a id="18436" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18440" href="plfa.Relations.html#18397" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="18445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18445" class="InductiveConstructor">s&lt;s</a> <a id="18449" class="Symbol">:</a> <a id="18451" class="Symbol">∀</a> <a id="18453" class="Symbol">{</a><a id="18454" href="plfa.Relations.html#18454" class="Bound">m</a> <a id="18456" href="plfa.Relations.html#18456" class="Bound">n</a> <a id="18458" class="Symbol">:</a> <a id="18460" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18461" class="Symbol">}</a>
    <a id="18467" class="Symbol">→</a> <a id="18469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18454" class="Bound">m</a> <a id="18471" href="plfa.Relations.html#18361" class="Datatype Operator">&lt;</a> <a id="18473" href="plfa.Relations.html#18456" class="Bound">n</a>
      <a id="18481" class="Comment">-------------</a>
    <a id="18499" class="Symbol">→</a> <a id="18501" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18454" class="Bound">m</a> <a id="18507" href="plfa.Relations.html#18361" class="Datatype Operator">&lt;</a> <a id="18509" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18513" href="plfa.Relations.html#18456" class="Bound">n</a>
</pre>{% endraw %}The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}/Negation/).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

{% raw %}<pre class="Agda"><a id="19682" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}/Negation/).)

{% raw %}<pre class="Agda"><a id="20170" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

{% raw %}<pre class="Agda"><a id="20379" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

{% raw %}<pre class="Agda"><a id="20522" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

{% raw %}<pre class="Agda"><a id="20782" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
{% raw %}<pre class="Agda"><a id="21021" class="Keyword">data</a> <a id="even"></a><a id="21026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21026" class="Datatype">even</a> <a id="21031" class="Symbol">:</a> <a id="21033" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21035" class="Symbol">→</a> <a id="21037" class="PrimitiveType">Set</a>
<a id="21041" class="Keyword">data</a> <a id="odd"></a><a id="21046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21046" class="Datatype">odd</a>  <a id="21051" class="Symbol">:</a> <a id="21053" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21055" class="Symbol">→</a> <a id="21057" class="PrimitiveType">Set</a>

<a id="21062" class="Keyword">data</a> <a id="21067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21026" class="Datatype">even</a> <a id="21072" class="Keyword">where</a>

  <a id="even.zero"></a><a id="21081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21081" class="InductiveConstructor">zero</a> <a id="21086" class="Symbol">:</a>
      <a id="21094" class="Comment">---------</a>
      <a id="21110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21026" class="Datatype">even</a> <a id="21115" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="21123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21123" class="InductiveConstructor">suc</a>  <a id="21128" class="Symbol">:</a> <a id="21130" class="Symbol">∀</a> <a id="21132" class="Symbol">{</a><a id="21133" href="plfa.Relations.html#21133" class="Bound">n</a> <a id="21135" class="Symbol">:</a> <a id="21137" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21138" class="Symbol">}</a>
    <a id="21144" class="Symbol">→</a> <a id="21146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21046" class="Datatype">odd</a> <a id="21150" href="plfa.Relations.html#21133" class="Bound">n</a>
      <a id="21158" class="Comment">------------</a>
    <a id="21175" class="Symbol">→</a> <a id="21177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21026" class="Datatype">even</a> <a id="21182" class="Symbol">(</a><a id="21183" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21187" href="plfa.Relations.html#21133" class="Bound">n</a><a id="21188" class="Symbol">)</a>

<a id="21191" class="Keyword">data</a> <a id="21196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21046" class="Datatype">odd</a> <a id="21200" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="21209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21209" class="InductiveConstructor">suc</a>   <a id="21215" class="Symbol">:</a> <a id="21217" class="Symbol">∀</a> <a id="21219" class="Symbol">{</a><a id="21220" href="plfa.Relations.html#21220" class="Bound">n</a> <a id="21222" class="Symbol">:</a> <a id="21224" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21225" class="Symbol">}</a>
    <a id="21231" class="Symbol">→</a> <a id="21233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21026" class="Datatype">even</a> <a id="21238" href="plfa.Relations.html#21220" class="Bound">n</a>
      <a id="21246" class="Comment">-----------</a>
    <a id="21262" class="Symbol">→</a> <a id="21264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21046" class="Datatype">odd</a> <a id="21268" class="Symbol">(</a><a id="21269" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21273" href="plfa.Relations.html#21220" class="Bound">n</a><a id="21274" class="Symbol">)</a>
</pre>{% endraw %}A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
{% raw %}<pre class="Agda"><a id="e+e≡e"></a><a id="22434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22434" class="Function">e+e≡e</a> <a id="22440" class="Symbol">:</a> <a id="22442" class="Symbol">∀</a> <a id="22444" class="Symbol">{</a><a id="22445" href="plfa.Relations.html#22445" class="Bound">m</a> <a id="22447" href="plfa.Relations.html#22447" class="Bound">n</a> <a id="22449" class="Symbol">:</a> <a id="22451" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22452" class="Symbol">}</a>
  <a id="22456" class="Symbol">→</a> <a id="22458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21026" class="Datatype">even</a> <a id="22463" href="plfa.Relations.html#22445" class="Bound">m</a>
  <a id="22467" class="Symbol">→</a> <a id="22469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21026" class="Datatype">even</a> <a id="22474" href="plfa.Relations.html#22447" class="Bound">n</a>
    <a id="22480" class="Comment">------------</a>
  <a id="22495" class="Symbol">→</a> <a id="22497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21026" class="Datatype">even</a> <a id="22502" class="Symbol">(</a><a id="22503" href="plfa.Relations.html#22445" class="Bound">m</a> <a id="22505" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22507" href="plfa.Relations.html#22447" class="Bound">n</a><a id="22508" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="22511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22511" class="Function">o+e≡o</a> <a id="22517" class="Symbol">:</a> <a id="22519" class="Symbol">∀</a> <a id="22521" class="Symbol">{</a><a id="22522" href="plfa.Relations.html#22522" class="Bound">m</a> <a id="22524" href="plfa.Relations.html#22524" class="Bound">n</a> <a id="22526" class="Symbol">:</a> <a id="22528" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22529" class="Symbol">}</a>
  <a id="22533" class="Symbol">→</a> <a id="22535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21046" class="Datatype">odd</a> <a id="22539" href="plfa.Relations.html#22522" class="Bound">m</a>
  <a id="22543" class="Symbol">→</a> <a id="22545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21026" class="Datatype">even</a> <a id="22550" href="plfa.Relations.html#22524" class="Bound">n</a>
    <a id="22556" class="Comment">-----------</a>
  <a id="22570" class="Symbol">→</a> <a id="22572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21046" class="Datatype">odd</a> <a id="22576" class="Symbol">(</a><a id="22577" href="plfa.Relations.html#22522" class="Bound">m</a> <a id="22579" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22581" href="plfa.Relations.html#22524" class="Bound">n</a><a id="22582" class="Symbol">)</a>

<a id="22585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22434" class="Function">e+e≡e</a> <a id="22591" href="plfa.Relations.html#21081" class="InductiveConstructor">zero</a>     <a id="22600" href="plfa.Relations.html#22600" class="Bound">en</a>  <a id="22604" class="Symbol">=</a>  <a id="22607" href="plfa.Relations.html#22600" class="Bound">en</a>
<a id="22610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22434" class="Function">e+e≡e</a> <a id="22616" class="Symbol">(</a><a id="22617" href="plfa.Relations.html#21123" class="InductiveConstructor">suc</a> <a id="22621" href="plfa.Relations.html#22621" class="Bound">om</a><a id="22623" class="Symbol">)</a> <a id="22625" href="plfa.Relations.html#22625" class="Bound">en</a>  <a id="22629" class="Symbol">=</a>  <a id="22632" href="plfa.Relations.html#21123" class="InductiveConstructor">suc</a> <a id="22636" class="Symbol">(</a><a id="22637" href="plfa.Relations.html#22511" class="Function">o+e≡o</a> <a id="22643" href="plfa.Relations.html#22621" class="Bound">om</a> <a id="22646" href="plfa.Relations.html#22625" class="Bound">en</a><a id="22648" class="Symbol">)</a>

<a id="22651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22511" class="Function">o+e≡o</a> <a id="22657" class="Symbol">(</a><a id="22658" href="plfa.Relations.html#21209" class="InductiveConstructor">suc</a> <a id="22662" href="plfa.Relations.html#22662" class="Bound">em</a><a id="22664" class="Symbol">)</a> <a id="22666" href="plfa.Relations.html#22666" class="Bound">en</a>  <a id="22670" class="Symbol">=</a>  <a id="22673" href="plfa.Relations.html#21209" class="InductiveConstructor">suc</a> <a id="22677" class="Symbol">(</a><a id="22678" href="plfa.Relations.html#22434" class="Function">e+e≡e</a> <a id="22684" href="plfa.Relations.html#22662" class="Bound">em</a> <a id="22687" href="plfa.Relations.html#22666" class="Bound">en</a><a id="22689" class="Symbol">)</a>
</pre>{% endraw %}Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

{% raw %}<pre class="Agda"><a id="23827" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)

{% raw %}<pre class="Agda"><a id="25119" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="25255" class="Keyword">import</a> <a id="25262" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="25271" class="Keyword">using</a> <a id="25277" class="Symbol">(</a><a id="25278" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="25281" class="Symbol">;</a> <a id="25283" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="25286" class="Symbol">;</a> <a id="25288" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="25291" class="Symbol">)</a>
<a id="25293" class="Keyword">import</a> <a id="25300" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="25320" class="Keyword">using</a> <a id="25326" class="Symbol">(</a><a id="25327" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="25333" class="Symbol">;</a> <a id="25335" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="25342" class="Symbol">;</a> <a id="25344" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="25353" class="Symbol">;</a> <a id="25355" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="25362" class="Symbol">;</a>
                                  <a id="25398" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="25407" class="Symbol">;</a> <a id="25409" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="25418" class="Symbol">;</a> <a id="25420" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="25428" class="Symbol">)</a>
</pre>{% endraw %}In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}/Connectives/)),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
