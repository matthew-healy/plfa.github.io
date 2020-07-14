---
src       : "src/plfa/part1/Relations.lagda.md"
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

{% raw %}<pre class="Agda"><a id="161" class="Keyword">module</a> <a id="168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="189" class="Keyword">where</a>
</pre>{% endraw %}
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

{% raw %}<pre class="Agda"><a id="354" class="Keyword">import</a> <a id="361" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="399" class="Symbol">as</a> <a id="402" class="Module">Eq</a>
<a id="405" class="Keyword">open</a> <a id="410" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="413" class="Keyword">using</a> <a id="419" class="Symbol">(</a><a id="420" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="423" class="Symbol">;</a> <a id="425" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="429" class="Symbol">;</a> <a id="431" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="435" class="Symbol">)</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="458" class="Keyword">using</a> <a id="464" class="Symbol">(</a><a id="465" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="466" class="Symbol">;</a> <a id="468" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="472" class="Symbol">;</a> <a id="474" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="477" class="Symbol">;</a> <a id="479" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="482" class="Symbol">;</a> <a id="484" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="487" class="Symbol">)</a>
<a id="489" class="Keyword">open</a> <a id="494" class="Keyword">import</a> <a id="501" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="521" class="Keyword">using</a> <a id="527" class="Symbol">(</a><a id="528" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="534" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="1195" class="Keyword">data</a> <a id="_≤_"></a><a id="1200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1200" class="Datatype Operator">_≤_</a> <a id="1204" class="Symbol">:</a> <a id="1206" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1208" class="Symbol">→</a> <a id="1210" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1212" class="Symbol">→</a> <a id="1214" class="PrimitiveType">Set</a> <a id="1218" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1227" class="InductiveConstructor">z≤n</a> <a id="1231" class="Symbol">:</a> <a id="1233" class="Symbol">∀</a> <a id="1235" class="Symbol">{</a><a id="1236" href="plfa.part1.Relations.html#1236" class="Bound">n</a> <a id="1238" class="Symbol">:</a> <a id="1240" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1241" class="Symbol">}</a>
      <a id="1249" class="Comment">--------</a>
    <a id="1262" class="Symbol">→</a> <a id="1264" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1200" class="Datatype Operator">≤</a> <a id="1271" href="plfa.part1.Relations.html#1236" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1276" class="InductiveConstructor">s≤s</a> <a id="1280" class="Symbol">:</a> <a id="1282" class="Symbol">∀</a> <a id="1284" class="Symbol">{</a><a id="1285" href="plfa.part1.Relations.html#1285" class="Bound">m</a> <a id="1287" href="plfa.part1.Relations.html#1287" class="Bound">n</a> <a id="1289" class="Symbol">:</a> <a id="1291" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1292" class="Symbol">}</a>
    <a id="1298" class="Symbol">→</a> <a id="1300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1285" class="Bound">m</a> <a id="1302" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="1304" href="plfa.part1.Relations.html#1287" class="Bound">n</a>
      <a id="1312" class="Comment">-------------</a>
    <a id="1330" class="Symbol">→</a> <a id="1332" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1285" class="Bound">m</a> <a id="1338" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="1340" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1344" href="plfa.part1.Relations.html#1287" class="Bound">n</a>
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
{% raw %}<pre class="Agda"><a id="2606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#2606" class="Function">_</a> <a id="2608" class="Symbol">:</a> <a id="2610" class="Number">2</a> <a id="2612" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="2614" class="Number">4</a>
<a id="2616" class="Symbol">_</a> <a id="2618" class="Symbol">=</a> <a id="2620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1276" class="InductiveConstructor">s≤s</a> <a id="2624" class="Symbol">(</a><a id="2625" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="2629" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a><a id="2632" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="3611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#3611" class="Function">_</a> <a id="3613" class="Symbol">:</a> <a id="3615" class="Number">2</a> <a id="3617" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="3619" class="Number">4</a>
<a id="3621" class="Symbol">_</a> <a id="3623" class="Symbol">=</a> <a id="3625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1276" class="InductiveConstructor">s≤s</a> <a id="3629" class="Symbol">{</a><a id="3630" class="Number">1</a><a id="3631" class="Symbol">}</a> <a id="3633" class="Symbol">{</a><a id="3634" class="Number">3</a><a id="3635" class="Symbol">}</a> <a id="3637" class="Symbol">(</a><a id="3638" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="3642" class="Symbol">{</a><a id="3643" class="Number">0</a><a id="3644" class="Symbol">}</a> <a id="3646" class="Symbol">{</a><a id="3647" class="Number">2</a><a id="3648" class="Symbol">}</a> <a id="3650" class="Symbol">(</a><a id="3651" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a> <a id="3655" class="Symbol">{</a><a id="3656" class="Number">2</a><a id="3657" class="Symbol">}))</a>
</pre>{% endraw %}One may also identify implicit arguments by name:
{% raw %}<pre class="Agda"><a id="3719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#3719" class="Function">_</a> <a id="3721" class="Symbol">:</a> <a id="3723" class="Number">2</a> <a id="3725" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="3727" class="Number">4</a>
<a id="3729" class="Symbol">_</a> <a id="3731" class="Symbol">=</a> <a id="3733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1276" class="InductiveConstructor">s≤s</a> <a id="3737" class="Symbol">{</a><a id="3738" class="Argument">m</a> <a id="3740" class="Symbol">=</a> <a id="3742" class="Number">1</a><a id="3743" class="Symbol">}</a> <a id="3745" class="Symbol">{</a><a id="3746" class="Argument">n</a> <a id="3748" class="Symbol">=</a> <a id="3750" class="Number">3</a><a id="3751" class="Symbol">}</a> <a id="3753" class="Symbol">(</a><a id="3754" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="3758" class="Symbol">{</a><a id="3759" class="Argument">m</a> <a id="3761" class="Symbol">=</a> <a id="3763" class="Number">0</a><a id="3764" class="Symbol">}</a> <a id="3766" class="Symbol">{</a><a id="3767" class="Argument">n</a> <a id="3769" class="Symbol">=</a> <a id="3771" class="Number">2</a><a id="3772" class="Symbol">}</a> <a id="3774" class="Symbol">(</a><a id="3775" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a> <a id="3779" class="Symbol">{</a><a id="3780" class="Argument">n</a> <a id="3782" class="Symbol">=</a> <a id="3784" class="Number">2</a><a id="3785" class="Symbol">}))</a>
</pre>{% endraw %}In the latter format, you may only supply some implicit arguments:
{% raw %}<pre class="Agda"><a id="3864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#3864" class="Function">_</a> <a id="3866" class="Symbol">:</a> <a id="3868" class="Number">2</a> <a id="3870" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="3872" class="Number">4</a>
<a id="3874" class="Symbol">_</a> <a id="3876" class="Symbol">=</a> <a id="3878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1276" class="InductiveConstructor">s≤s</a> <a id="3882" class="Symbol">{</a><a id="3883" class="Argument">n</a> <a id="3885" class="Symbol">=</a> <a id="3887" class="Number">3</a><a id="3888" class="Symbol">}</a> <a id="3890" class="Symbol">(</a><a id="3891" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="3895" class="Symbol">{</a><a id="3896" class="Argument">n</a> <a id="3898" class="Symbol">=</a> <a id="3900" class="Number">2</a><a id="3901" class="Symbol">}</a> <a id="3903" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a><a id="3906" class="Symbol">)</a>
</pre>{% endraw %}It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows:
{% raw %}<pre class="Agda"><a id="4051" class="Keyword">infix</a> <a id="4057" class="Number">4</a> <a id="4059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1200" class="Datatype Operator">_≤_</a>
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
For instance, from `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
{% raw %}<pre class="Agda"><a id="inv-s≤s"></a><a id="5076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5076" class="Function">inv-s≤s</a> <a id="5084" class="Symbol">:</a> <a id="5086" class="Symbol">∀</a> <a id="5088" class="Symbol">{</a><a id="5089" href="plfa.part1.Relations.html#5089" class="Bound">m</a> <a id="5091" href="plfa.part1.Relations.html#5091" class="Bound">n</a> <a id="5093" class="Symbol">:</a> <a id="5095" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5096" class="Symbol">}</a>
  <a id="5100" class="Symbol">→</a> <a id="5102" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5089" class="Bound">m</a> <a id="5108" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="5110" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5114" href="plfa.part1.Relations.html#5091" class="Bound">n</a>
    <a id="5120" class="Comment">-------------</a>
  <a id="5136" class="Symbol">→</a> <a id="5138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5089" class="Bound">m</a> <a id="5140" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="5142" href="plfa.part1.Relations.html#5091" class="Bound">n</a>
<a id="5144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5076" class="Function">inv-s≤s</a> <a id="5152" class="Symbol">(</a><a id="5153" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="5157" href="plfa.part1.Relations.html#5157" class="Bound">m≤n</a><a id="5160" class="Symbol">)</a> <a id="5162" class="Symbol">=</a> <a id="5164" href="plfa.part1.Relations.html#5157" class="Bound">m≤n</a>
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
{% raw %}<pre class="Agda"><a id="inv-z≤n"></a><a id="5679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5679" class="Function">inv-z≤n</a> <a id="5687" class="Symbol">:</a> <a id="5689" class="Symbol">∀</a> <a id="5691" class="Symbol">{</a><a id="5692" href="plfa.part1.Relations.html#5692" class="Bound">m</a> <a id="5694" class="Symbol">:</a> <a id="5696" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5697" class="Symbol">}</a>
  <a id="5701" class="Symbol">→</a> <a id="5703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5692" class="Bound">m</a> <a id="5705" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="5707" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
    <a id="5716" class="Comment">--------</a>
  <a id="5727" class="Symbol">→</a> <a id="5729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5692" class="Bound">m</a> <a id="5731" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5733" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
<a id="5738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5679" class="Function">inv-z≤n</a> <a id="5746" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a> <a id="5750" class="Symbol">=</a> <a id="5752" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
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


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

{% raw %}<pre class="Agda"><a id="7254" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
Give an example of a partial order that is not a total order.

{% raw %}<pre class="Agda"><a id="7349" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{% raw %}<pre class="Agda"><a id="≤-refl"></a><a id="7649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7649" class="Function">≤-refl</a> <a id="7656" class="Symbol">:</a> <a id="7658" class="Symbol">∀</a> <a id="7660" class="Symbol">{</a><a id="7661" href="plfa.part1.Relations.html#7661" class="Bound">n</a> <a id="7663" class="Symbol">:</a> <a id="7665" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7666" class="Symbol">}</a>
    <a id="7672" class="Comment">-----</a>
  <a id="7680" class="Symbol">→</a> <a id="7682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7661" class="Bound">n</a> <a id="7684" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="7686" href="plfa.part1.Relations.html#7661" class="Bound">n</a>
<a id="7688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7649" class="Function">≤-refl</a> <a id="7695" class="Symbol">{</a><a id="7696" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="7700" class="Symbol">}</a> <a id="7702" class="Symbol">=</a> <a id="7704" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>
<a id="7708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7649" class="Function">≤-refl</a> <a id="7715" class="Symbol">{</a><a id="7716" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7720" href="plfa.part1.Relations.html#7720" class="Bound">n</a><a id="7721" class="Symbol">}</a> <a id="7723" class="Symbol">=</a> <a id="7725" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="7729" href="plfa.part1.Relations.html#7649" class="Function">≤-refl</a>
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
{% raw %}<pre class="Agda"><a id="≤-trans"></a><a id="8366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8366" class="Function">≤-trans</a> <a id="8374" class="Symbol">:</a> <a id="8376" class="Symbol">∀</a> <a id="8378" class="Symbol">{</a><a id="8379" href="plfa.part1.Relations.html#8379" class="Bound">m</a> <a id="8381" href="plfa.part1.Relations.html#8381" class="Bound">n</a> <a id="8383" href="plfa.part1.Relations.html#8383" class="Bound">p</a> <a id="8385" class="Symbol">:</a> <a id="8387" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8388" class="Symbol">}</a>
  <a id="8392" class="Symbol">→</a> <a id="8394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8379" class="Bound">m</a> <a id="8396" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="8398" href="plfa.part1.Relations.html#8381" class="Bound">n</a>
  <a id="8402" class="Symbol">→</a> <a id="8404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8381" class="Bound">n</a> <a id="8406" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="8408" href="plfa.part1.Relations.html#8383" class="Bound">p</a>
    <a id="8414" class="Comment">-----</a>
  <a id="8422" class="Symbol">→</a> <a id="8424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8379" class="Bound">m</a> <a id="8426" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="8428" href="plfa.part1.Relations.html#8383" class="Bound">p</a>
<a id="8430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8366" class="Function">≤-trans</a> <a id="8438" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>       <a id="8448" class="Symbol">_</a>          <a id="8459" class="Symbol">=</a>  <a id="8462" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>
<a id="8466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8366" class="Function">≤-trans</a> <a id="8474" class="Symbol">(</a><a id="8475" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="8479" href="plfa.part1.Relations.html#8479" class="Bound">m≤n</a><a id="8482" class="Symbol">)</a> <a id="8484" class="Symbol">(</a><a id="8485" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="8489" href="plfa.part1.Relations.html#8489" class="Bound">n≤p</a><a id="8492" class="Symbol">)</a>  <a id="8495" class="Symbol">=</a>  <a id="8498" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="8502" class="Symbol">(</a><a id="8503" href="plfa.part1.Relations.html#8366" class="Function">≤-trans</a> <a id="8511" href="plfa.part1.Relations.html#8479" class="Bound">m≤n</a> <a id="8515" href="plfa.part1.Relations.html#8489" class="Bound">n≤p</a><a id="8518" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="≤-trans′"></a><a id="9479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9479" class="Function">≤-trans′</a> <a id="9488" class="Symbol">:</a> <a id="9490" class="Symbol">∀</a> <a id="9492" class="Symbol">(</a><a id="9493" href="plfa.part1.Relations.html#9493" class="Bound">m</a> <a id="9495" href="plfa.part1.Relations.html#9495" class="Bound">n</a> <a id="9497" href="plfa.part1.Relations.html#9497" class="Bound">p</a> <a id="9499" class="Symbol">:</a> <a id="9501" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9502" class="Symbol">)</a>
  <a id="9506" class="Symbol">→</a> <a id="9508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9493" class="Bound">m</a> <a id="9510" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="9512" href="plfa.part1.Relations.html#9495" class="Bound">n</a>
  <a id="9516" class="Symbol">→</a> <a id="9518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9495" class="Bound">n</a> <a id="9520" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="9522" href="plfa.part1.Relations.html#9497" class="Bound">p</a>
    <a id="9528" class="Comment">-----</a>
  <a id="9536" class="Symbol">→</a> <a id="9538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9493" class="Bound">m</a> <a id="9540" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="9542" href="plfa.part1.Relations.html#9497" class="Bound">p</a>
<a id="9544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9479" class="Function">≤-trans′</a> <a id="9553" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="9561" class="Symbol">_</a>       <a id="9569" class="Symbol">_</a>       <a id="9577" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>       <a id="9587" class="Symbol">_</a>          <a id="9598" class="Symbol">=</a>  <a id="9601" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>
<a id="9605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9479" class="Function">≤-trans′</a> <a id="9614" class="Symbol">(</a><a id="9615" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9619" href="plfa.part1.Relations.html#9619" class="Bound">m</a><a id="9620" class="Symbol">)</a> <a id="9622" class="Symbol">(</a><a id="9623" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9627" href="plfa.part1.Relations.html#9627" class="Bound">n</a><a id="9628" class="Symbol">)</a> <a id="9630" class="Symbol">(</a><a id="9631" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9635" href="plfa.part1.Relations.html#9635" class="Bound">p</a><a id="9636" class="Symbol">)</a> <a id="9638" class="Symbol">(</a><a id="9639" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="9643" href="plfa.part1.Relations.html#9643" class="Bound">m≤n</a><a id="9646" class="Symbol">)</a> <a id="9648" class="Symbol">(</a><a id="9649" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="9653" href="plfa.part1.Relations.html#9653" class="Bound">n≤p</a><a id="9656" class="Symbol">)</a>  <a id="9659" class="Symbol">=</a>  <a id="9662" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="9666" class="Symbol">(</a><a id="9667" href="plfa.part1.Relations.html#9479" class="Function">≤-trans′</a> <a id="9676" href="plfa.part1.Relations.html#9619" class="Bound">m</a> <a id="9678" href="plfa.part1.Relations.html#9627" class="Bound">n</a> <a id="9680" href="plfa.part1.Relations.html#9635" class="Bound">p</a> <a id="9682" href="plfa.part1.Relations.html#9643" class="Bound">m≤n</a> <a id="9686" href="plfa.part1.Relations.html#9653" class="Bound">n≤p</a><a id="9689" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="≤-antisym"></a><a id="10434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10434" class="Function">≤-antisym</a> <a id="10444" class="Symbol">:</a> <a id="10446" class="Symbol">∀</a> <a id="10448" class="Symbol">{</a><a id="10449" href="plfa.part1.Relations.html#10449" class="Bound">m</a> <a id="10451" href="plfa.part1.Relations.html#10451" class="Bound">n</a> <a id="10453" class="Symbol">:</a> <a id="10455" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10456" class="Symbol">}</a>
  <a id="10460" class="Symbol">→</a> <a id="10462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10449" class="Bound">m</a> <a id="10464" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="10466" href="plfa.part1.Relations.html#10451" class="Bound">n</a>
  <a id="10470" class="Symbol">→</a> <a id="10472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10451" class="Bound">n</a> <a id="10474" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="10476" href="plfa.part1.Relations.html#10449" class="Bound">m</a>
    <a id="10482" class="Comment">-----</a>
  <a id="10490" class="Symbol">→</a> <a id="10492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10449" class="Bound">m</a> <a id="10494" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10496" href="plfa.part1.Relations.html#10451" class="Bound">n</a>
<a id="10498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10434" class="Function">≤-antisym</a> <a id="10508" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>       <a id="10518" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>        <a id="10529" class="Symbol">=</a>  <a id="10532" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="10537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10434" class="Function">≤-antisym</a> <a id="10547" class="Symbol">(</a><a id="10548" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="10552" href="plfa.part1.Relations.html#10552" class="Bound">m≤n</a><a id="10555" class="Symbol">)</a> <a id="10557" class="Symbol">(</a><a id="10558" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="10562" href="plfa.part1.Relations.html#10562" class="Bound">n≤m</a><a id="10565" class="Symbol">)</a>  <a id="10568" class="Symbol">=</a>  <a id="10571" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="10576" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10580" class="Symbol">(</a><a id="10581" href="plfa.part1.Relations.html#10434" class="Function">≤-antisym</a> <a id="10591" href="plfa.part1.Relations.html#10552" class="Bound">m≤n</a> <a id="10595" href="plfa.part1.Relations.html#10562" class="Bound">n≤m</a><a id="10598" class="Symbol">)</a>
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

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

{% raw %}<pre class="Agda"><a id="11404" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
{% raw %}<pre class="Agda"><a id="11658" class="Keyword">data</a> <a id="Total"></a><a id="11663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11663" class="Datatype">Total</a> <a id="11669" class="Symbol">(</a><a id="11670" href="plfa.part1.Relations.html#11670" class="Bound">m</a> <a id="11672" href="plfa.part1.Relations.html#11672" class="Bound">n</a> <a id="11674" class="Symbol">:</a> <a id="11676" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11677" class="Symbol">)</a> <a id="11679" class="Symbol">:</a> <a id="11681" class="PrimitiveType">Set</a> <a id="11685" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="11694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11694" class="InductiveConstructor">forward</a> <a id="11702" class="Symbol">:</a>
      <a id="11710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11670" class="Bound">m</a> <a id="11712" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="11714" href="plfa.part1.Relations.html#11672" class="Bound">n</a>
      <a id="11722" class="Comment">---------</a>
    <a id="11736" class="Symbol">→</a> <a id="11738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11663" class="Datatype">Total</a> <a id="11744" href="plfa.part1.Relations.html#11670" class="Bound">m</a> <a id="11746" href="plfa.part1.Relations.html#11672" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="11751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11751" class="InductiveConstructor">flipped</a> <a id="11759" class="Symbol">:</a>
      <a id="11767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11672" class="Bound">n</a> <a id="11769" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="11771" href="plfa.part1.Relations.html#11670" class="Bound">m</a>
      <a id="11779" class="Comment">---------</a>
    <a id="11793" class="Symbol">→</a> <a id="11795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11663" class="Datatype">Total</a> <a id="11801" href="plfa.part1.Relations.html#11670" class="Bound">m</a> <a id="11803" href="plfa.part1.Relations.html#11672" class="Bound">n</a>
</pre>{% endraw %}Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}/Connectives/).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{% raw %}<pre class="Agda"><a id="12292" class="Keyword">data</a> <a id="Total′"></a><a id="12297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12297" class="Datatype">Total′</a> <a id="12304" class="Symbol">:</a> <a id="12306" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12308" class="Symbol">→</a> <a id="12310" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12312" class="Symbol">→</a> <a id="12314" class="PrimitiveType">Set</a> <a id="12318" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="12327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12327" class="InductiveConstructor">forward′</a> <a id="12336" class="Symbol">:</a> <a id="12338" class="Symbol">∀</a> <a id="12340" class="Symbol">{</a><a id="12341" href="plfa.part1.Relations.html#12341" class="Bound">m</a> <a id="12343" href="plfa.part1.Relations.html#12343" class="Bound">n</a> <a id="12345" class="Symbol">:</a> <a id="12347" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12348" class="Symbol">}</a>
    <a id="12354" class="Symbol">→</a> <a id="12356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12341" class="Bound">m</a> <a id="12358" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="12360" href="plfa.part1.Relations.html#12343" class="Bound">n</a>
      <a id="12368" class="Comment">----------</a>
    <a id="12383" class="Symbol">→</a> <a id="12385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12297" class="Datatype">Total′</a> <a id="12392" href="plfa.part1.Relations.html#12341" class="Bound">m</a> <a id="12394" href="plfa.part1.Relations.html#12343" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="12399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12399" class="InductiveConstructor">flipped′</a> <a id="12408" class="Symbol">:</a> <a id="12410" class="Symbol">∀</a> <a id="12412" class="Symbol">{</a><a id="12413" href="plfa.part1.Relations.html#12413" class="Bound">m</a> <a id="12415" href="plfa.part1.Relations.html#12415" class="Bound">n</a> <a id="12417" class="Symbol">:</a> <a id="12419" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12420" class="Symbol">}</a>
    <a id="12426" class="Symbol">→</a> <a id="12428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12415" class="Bound">n</a> <a id="12430" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="12432" href="plfa.part1.Relations.html#12413" class="Bound">m</a>
      <a id="12440" class="Comment">----------</a>
    <a id="12455" class="Symbol">→</a> <a id="12457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12297" class="Datatype">Total′</a> <a id="12464" href="plfa.part1.Relations.html#12413" class="Bound">m</a> <a id="12466" href="plfa.part1.Relations.html#12415" class="Bound">n</a>
</pre>{% endraw %}Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
{% raw %}<pre class="Agda"><a id="≤-total"></a><a id="12985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12985" class="Function">≤-total</a> <a id="12993" class="Symbol">:</a> <a id="12995" class="Symbol">∀</a> <a id="12997" class="Symbol">(</a><a id="12998" href="plfa.part1.Relations.html#12998" class="Bound">m</a> <a id="13000" href="plfa.part1.Relations.html#13000" class="Bound">n</a> <a id="13002" class="Symbol">:</a> <a id="13004" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13005" class="Symbol">)</a> <a id="13007" class="Symbol">→</a> <a id="13009" href="plfa.part1.Relations.html#11663" class="Datatype">Total</a> <a id="13015" href="plfa.part1.Relations.html#12998" class="Bound">m</a> <a id="13017" href="plfa.part1.Relations.html#13000" class="Bound">n</a>
<a id="13019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12985" class="Function">≤-total</a> <a id="13027" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="13035" href="plfa.part1.Relations.html#13035" class="Bound">n</a>                         <a id="13061" class="Symbol">=</a>  <a id="13064" href="plfa.part1.Relations.html#11694" class="InductiveConstructor">forward</a> <a id="13072" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>
<a id="13076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12985" class="Function">≤-total</a> <a id="13084" class="Symbol">(</a><a id="13085" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13089" href="plfa.part1.Relations.html#13089" class="Bound">m</a><a id="13090" class="Symbol">)</a> <a id="13092" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="13118" class="Symbol">=</a>  <a id="13121" href="plfa.part1.Relations.html#11751" class="InductiveConstructor">flipped</a> <a id="13129" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>
<a id="13133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12985" class="Function">≤-total</a> <a id="13141" class="Symbol">(</a><a id="13142" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13146" href="plfa.part1.Relations.html#13146" class="Bound">m</a><a id="13147" class="Symbol">)</a> <a id="13149" class="Symbol">(</a><a id="13150" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13154" href="plfa.part1.Relations.html#13154" class="Bound">n</a><a id="13155" class="Symbol">)</a> <a id="13157" class="Keyword">with</a> <a id="13162" href="plfa.part1.Relations.html#12985" class="Function">≤-total</a> <a id="13170" href="plfa.part1.Relations.html#13146" class="Bound">m</a> <a id="13172" href="plfa.part1.Relations.html#13154" class="Bound">n</a>
<a id="13174" class="Symbol">...</a>                        <a id="13201" class="Symbol">|</a> <a id="13203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11694" class="InductiveConstructor">forward</a> <a id="13211" href="plfa.part1.Relations.html#13211" class="Bound">m≤n</a>  <a id="13216" class="Symbol">=</a>  <a id="13219" href="plfa.part1.Relations.html#11694" class="InductiveConstructor">forward</a> <a id="13227" class="Symbol">(</a><a id="13228" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="13232" href="plfa.part1.Relations.html#13211" class="Bound">m≤n</a><a id="13235" class="Symbol">)</a>
<a id="13237" class="Symbol">...</a>                        <a id="13264" class="Symbol">|</a> <a id="13266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11751" class="InductiveConstructor">flipped</a> <a id="13274" href="plfa.part1.Relations.html#13274" class="Bound">n≤m</a>  <a id="13279" class="Symbol">=</a>  <a id="13282" href="plfa.part1.Relations.html#11751" class="InductiveConstructor">flipped</a> <a id="13290" class="Symbol">(</a><a id="13291" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="13295" href="plfa.part1.Relations.html#13274" class="Bound">n≤m</a><a id="13298" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="≤-total′"></a><a id="14790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14790" class="Function">≤-total′</a> <a id="14799" class="Symbol">:</a> <a id="14801" class="Symbol">∀</a> <a id="14803" class="Symbol">(</a><a id="14804" href="plfa.part1.Relations.html#14804" class="Bound">m</a> <a id="14806" href="plfa.part1.Relations.html#14806" class="Bound">n</a> <a id="14808" class="Symbol">:</a> <a id="14810" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14811" class="Symbol">)</a> <a id="14813" class="Symbol">→</a> <a id="14815" href="plfa.part1.Relations.html#11663" class="Datatype">Total</a> <a id="14821" href="plfa.part1.Relations.html#14804" class="Bound">m</a> <a id="14823" href="plfa.part1.Relations.html#14806" class="Bound">n</a>
<a id="14825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14790" class="Function">≤-total′</a> <a id="14834" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="14842" href="plfa.part1.Relations.html#14842" class="Bound">n</a>        <a id="14851" class="Symbol">=</a>  <a id="14854" href="plfa.part1.Relations.html#11694" class="InductiveConstructor">forward</a> <a id="14862" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>
<a id="14866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14790" class="Function">≤-total′</a> <a id="14875" class="Symbol">(</a><a id="14876" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14880" href="plfa.part1.Relations.html#14880" class="Bound">m</a><a id="14881" class="Symbol">)</a> <a id="14883" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="14892" class="Symbol">=</a>  <a id="14895" href="plfa.part1.Relations.html#11751" class="InductiveConstructor">flipped</a> <a id="14903" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>
<a id="14907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14790" class="Function">≤-total′</a> <a id="14916" class="Symbol">(</a><a id="14917" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14921" href="plfa.part1.Relations.html#14921" class="Bound">m</a><a id="14922" class="Symbol">)</a> <a id="14924" class="Symbol">(</a><a id="14925" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14929" href="plfa.part1.Relations.html#14929" class="Bound">n</a><a id="14930" class="Symbol">)</a>  <a id="14933" class="Symbol">=</a>  <a id="14936" href="plfa.part1.Relations.html#14968" class="Function">helper</a> <a id="14943" class="Symbol">(</a><a id="14944" href="plfa.part1.Relations.html#14790" class="Function">≤-total′</a> <a id="14953" href="plfa.part1.Relations.html#14921" class="Bound">m</a> <a id="14955" href="plfa.part1.Relations.html#14929" class="Bound">n</a><a id="14956" class="Symbol">)</a>
  <a id="14960" class="Keyword">where</a>
  <a id="14968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14968" class="Function">helper</a> <a id="14975" class="Symbol">:</a> <a id="14977" href="plfa.part1.Relations.html#11663" class="Datatype">Total</a> <a id="14983" href="plfa.part1.Relations.html#14921" class="Bound">m</a> <a id="14985" href="plfa.part1.Relations.html#14929" class="Bound">n</a> <a id="14987" class="Symbol">→</a> <a id="14989" href="plfa.part1.Relations.html#11663" class="Datatype">Total</a> <a id="14995" class="Symbol">(</a><a id="14996" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15000" href="plfa.part1.Relations.html#14921" class="Bound">m</a><a id="15001" class="Symbol">)</a> <a id="15003" class="Symbol">(</a><a id="15004" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15008" href="plfa.part1.Relations.html#14929" class="Bound">n</a><a id="15009" class="Symbol">)</a>
  <a id="15013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14968" class="Function">helper</a> <a id="15020" class="Symbol">(</a><a id="15021" href="plfa.part1.Relations.html#11694" class="InductiveConstructor">forward</a> <a id="15029" href="plfa.part1.Relations.html#15029" class="Bound">m≤n</a><a id="15032" class="Symbol">)</a>  <a id="15035" class="Symbol">=</a>  <a id="15038" href="plfa.part1.Relations.html#11694" class="InductiveConstructor">forward</a> <a id="15046" class="Symbol">(</a><a id="15047" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="15051" href="plfa.part1.Relations.html#15029" class="Bound">m≤n</a><a id="15054" class="Symbol">)</a>
  <a id="15058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14968" class="Function">helper</a> <a id="15065" class="Symbol">(</a><a id="15066" href="plfa.part1.Relations.html#11751" class="InductiveConstructor">flipped</a> <a id="15074" href="plfa.part1.Relations.html#15074" class="Bound">n≤m</a><a id="15077" class="Symbol">)</a>  <a id="15080" class="Symbol">=</a>  <a id="15083" href="plfa.part1.Relations.html#11751" class="InductiveConstructor">flipped</a> <a id="15091" class="Symbol">(</a><a id="15092" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="15096" href="plfa.part1.Relations.html#15074" class="Bound">n≤m</a><a id="15099" class="Symbol">)</a>
</pre>{% endraw %}This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{% raw %}<pre class="Agda"><a id="≤-total″"></a><a id="15721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15721" class="Function">≤-total″</a> <a id="15730" class="Symbol">:</a> <a id="15732" class="Symbol">∀</a> <a id="15734" class="Symbol">(</a><a id="15735" href="plfa.part1.Relations.html#15735" class="Bound">m</a> <a id="15737" href="plfa.part1.Relations.html#15737" class="Bound">n</a> <a id="15739" class="Symbol">:</a> <a id="15741" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15742" class="Symbol">)</a> <a id="15744" class="Symbol">→</a> <a id="15746" href="plfa.part1.Relations.html#11663" class="Datatype">Total</a> <a id="15752" href="plfa.part1.Relations.html#15735" class="Bound">m</a> <a id="15754" href="plfa.part1.Relations.html#15737" class="Bound">n</a>
<a id="15756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15721" class="Function">≤-total″</a> <a id="15765" href="plfa.part1.Relations.html#15765" class="Bound">m</a>       <a id="15773" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="15799" class="Symbol">=</a>  <a id="15802" href="plfa.part1.Relations.html#11751" class="InductiveConstructor">flipped</a> <a id="15810" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>
<a id="15814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15721" class="Function">≤-total″</a> <a id="15823" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="15831" class="Symbol">(</a><a id="15832" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15836" href="plfa.part1.Relations.html#15836" class="Bound">n</a><a id="15837" class="Symbol">)</a>                   <a id="15857" class="Symbol">=</a>  <a id="15860" href="plfa.part1.Relations.html#11694" class="InductiveConstructor">forward</a> <a id="15868" href="plfa.part1.Relations.html#1227" class="InductiveConstructor">z≤n</a>
<a id="15872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15721" class="Function">≤-total″</a> <a id="15881" class="Symbol">(</a><a id="15882" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15886" href="plfa.part1.Relations.html#15886" class="Bound">m</a><a id="15887" class="Symbol">)</a> <a id="15889" class="Symbol">(</a><a id="15890" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15894" href="plfa.part1.Relations.html#15894" class="Bound">n</a><a id="15895" class="Symbol">)</a> <a id="15897" class="Keyword">with</a> <a id="15902" href="plfa.part1.Relations.html#15721" class="Function">≤-total″</a> <a id="15911" href="plfa.part1.Relations.html#15886" class="Bound">m</a> <a id="15913" href="plfa.part1.Relations.html#15894" class="Bound">n</a>
<a id="15915" class="Symbol">...</a>                        <a id="15942" class="Symbol">|</a> <a id="15944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11694" class="InductiveConstructor">forward</a> <a id="15952" href="plfa.part1.Relations.html#15952" class="Bound">m≤n</a>   <a id="15958" class="Symbol">=</a>  <a id="15961" href="plfa.part1.Relations.html#11694" class="InductiveConstructor">forward</a> <a id="15969" class="Symbol">(</a><a id="15970" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="15974" href="plfa.part1.Relations.html#15952" class="Bound">m≤n</a><a id="15977" class="Symbol">)</a>
<a id="15979" class="Symbol">...</a>                        <a id="16006" class="Symbol">|</a> <a id="16008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11751" class="InductiveConstructor">flipped</a> <a id="16016" href="plfa.part1.Relations.html#16016" class="Bound">n≤m</a>   <a id="16022" class="Symbol">=</a>  <a id="16025" href="plfa.part1.Relations.html#11751" class="InductiveConstructor">flipped</a> <a id="16033" class="Symbol">(</a><a id="16034" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="16038" href="plfa.part1.Relations.html#16016" class="Bound">n≤m</a><a id="16041" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="+-monoʳ-≤"></a><a id="16630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16630" class="Function">+-monoʳ-≤</a> <a id="16640" class="Symbol">:</a> <a id="16642" class="Symbol">∀</a> <a id="16644" class="Symbol">(</a><a id="16645" href="plfa.part1.Relations.html#16645" class="Bound">n</a> <a id="16647" href="plfa.part1.Relations.html#16647" class="Bound">p</a> <a id="16649" href="plfa.part1.Relations.html#16649" class="Bound">q</a> <a id="16651" class="Symbol">:</a> <a id="16653" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16654" class="Symbol">)</a>
  <a id="16658" class="Symbol">→</a> <a id="16660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16647" class="Bound">p</a> <a id="16662" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="16664" href="plfa.part1.Relations.html#16649" class="Bound">q</a>
    <a id="16670" class="Comment">-------------</a>
  <a id="16686" class="Symbol">→</a> <a id="16688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16645" class="Bound">n</a> <a id="16690" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16692" href="plfa.part1.Relations.html#16647" class="Bound">p</a> <a id="16694" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="16696" href="plfa.part1.Relations.html#16645" class="Bound">n</a> <a id="16698" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16700" href="plfa.part1.Relations.html#16649" class="Bound">q</a>
<a id="16702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16630" class="Function">+-monoʳ-≤</a> <a id="16712" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="16720" href="plfa.part1.Relations.html#16720" class="Bound">p</a> <a id="16722" href="plfa.part1.Relations.html#16722" class="Bound">q</a> <a id="16724" href="plfa.part1.Relations.html#16724" class="Bound">p≤q</a>  <a id="16729" class="Symbol">=</a>  <a id="16732" href="plfa.part1.Relations.html#16724" class="Bound">p≤q</a>
<a id="16736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16630" class="Function">+-monoʳ-≤</a> <a id="16746" class="Symbol">(</a><a id="16747" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16751" href="plfa.part1.Relations.html#16751" class="Bound">n</a><a id="16752" class="Symbol">)</a> <a id="16754" href="plfa.part1.Relations.html#16754" class="Bound">p</a> <a id="16756" href="plfa.part1.Relations.html#16756" class="Bound">q</a> <a id="16758" href="plfa.part1.Relations.html#16758" class="Bound">p≤q</a>  <a id="16763" class="Symbol">=</a>  <a id="16766" href="plfa.part1.Relations.html#1276" class="InductiveConstructor">s≤s</a> <a id="16770" class="Symbol">(</a><a id="16771" href="plfa.part1.Relations.html#16630" class="Function">+-monoʳ-≤</a> <a id="16781" href="plfa.part1.Relations.html#16751" class="Bound">n</a> <a id="16783" href="plfa.part1.Relations.html#16754" class="Bound">p</a> <a id="16785" href="plfa.part1.Relations.html#16756" class="Bound">q</a> <a id="16787" href="plfa.part1.Relations.html#16758" class="Bound">p≤q</a><a id="16790" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="+-monoˡ-≤"></a><a id="17430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17430" class="Function">+-monoˡ-≤</a> <a id="17440" class="Symbol">:</a> <a id="17442" class="Symbol">∀</a> <a id="17444" class="Symbol">(</a><a id="17445" href="plfa.part1.Relations.html#17445" class="Bound">m</a> <a id="17447" href="plfa.part1.Relations.html#17447" class="Bound">n</a> <a id="17449" href="plfa.part1.Relations.html#17449" class="Bound">p</a> <a id="17451" class="Symbol">:</a> <a id="17453" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17454" class="Symbol">)</a>
  <a id="17458" class="Symbol">→</a> <a id="17460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17445" class="Bound">m</a> <a id="17462" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="17464" href="plfa.part1.Relations.html#17447" class="Bound">n</a>
    <a id="17470" class="Comment">-------------</a>
  <a id="17486" class="Symbol">→</a> <a id="17488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17445" class="Bound">m</a> <a id="17490" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17492" href="plfa.part1.Relations.html#17449" class="Bound">p</a> <a id="17494" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="17496" href="plfa.part1.Relations.html#17447" class="Bound">n</a> <a id="17498" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17500" href="plfa.part1.Relations.html#17449" class="Bound">p</a>
<a id="17502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17430" class="Function">+-monoˡ-≤</a> <a id="17512" href="plfa.part1.Relations.html#17512" class="Bound">m</a> <a id="17514" href="plfa.part1.Relations.html#17514" class="Bound">n</a> <a id="17516" href="plfa.part1.Relations.html#17516" class="Bound">p</a> <a id="17518" href="plfa.part1.Relations.html#17518" class="Bound">m≤n</a>  <a id="17523" class="Keyword">rewrite</a> <a id="17531" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17538" href="plfa.part1.Relations.html#17512" class="Bound">m</a> <a id="17540" href="plfa.part1.Relations.html#17516" class="Bound">p</a> <a id="17542" class="Symbol">|</a> <a id="17544" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17551" href="plfa.part1.Relations.html#17514" class="Bound">n</a> <a id="17553" href="plfa.part1.Relations.html#17516" class="Bound">p</a>  <a id="17556" class="Symbol">=</a> <a id="17558" href="plfa.part1.Relations.html#16630" class="Function">+-monoʳ-≤</a> <a id="17568" href="plfa.part1.Relations.html#17516" class="Bound">p</a> <a id="17570" href="plfa.part1.Relations.html#17512" class="Bound">m</a> <a id="17572" href="plfa.part1.Relations.html#17514" class="Bound">n</a> <a id="17574" href="plfa.part1.Relations.html#17518" class="Bound">m≤n</a>
</pre>{% endraw %}Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
{% raw %}<pre class="Agda"><a id="+-mono-≤"></a><a id="17772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17772" class="Function">+-mono-≤</a> <a id="17781" class="Symbol">:</a> <a id="17783" class="Symbol">∀</a> <a id="17785" class="Symbol">(</a><a id="17786" href="plfa.part1.Relations.html#17786" class="Bound">m</a> <a id="17788" href="plfa.part1.Relations.html#17788" class="Bound">n</a> <a id="17790" href="plfa.part1.Relations.html#17790" class="Bound">p</a> <a id="17792" href="plfa.part1.Relations.html#17792" class="Bound">q</a> <a id="17794" class="Symbol">:</a> <a id="17796" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17797" class="Symbol">)</a>
  <a id="17801" class="Symbol">→</a> <a id="17803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17786" class="Bound">m</a> <a id="17805" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="17807" href="plfa.part1.Relations.html#17788" class="Bound">n</a>
  <a id="17811" class="Symbol">→</a> <a id="17813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17790" class="Bound">p</a> <a id="17815" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="17817" href="plfa.part1.Relations.html#17792" class="Bound">q</a>
    <a id="17823" class="Comment">-------------</a>
  <a id="17839" class="Symbol">→</a> <a id="17841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17786" class="Bound">m</a> <a id="17843" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17845" href="plfa.part1.Relations.html#17790" class="Bound">p</a> <a id="17847" href="plfa.part1.Relations.html#1200" class="Datatype Operator">≤</a> <a id="17849" href="plfa.part1.Relations.html#17788" class="Bound">n</a> <a id="17851" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17853" href="plfa.part1.Relations.html#17792" class="Bound">q</a>
<a id="17855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17772" class="Function">+-mono-≤</a> <a id="17864" href="plfa.part1.Relations.html#17864" class="Bound">m</a> <a id="17866" href="plfa.part1.Relations.html#17866" class="Bound">n</a> <a id="17868" href="plfa.part1.Relations.html#17868" class="Bound">p</a> <a id="17870" href="plfa.part1.Relations.html#17870" class="Bound">q</a> <a id="17872" href="plfa.part1.Relations.html#17872" class="Bound">m≤n</a> <a id="17876" href="plfa.part1.Relations.html#17876" class="Bound">p≤q</a>  <a id="17881" class="Symbol">=</a>  <a id="17884" href="plfa.part1.Relations.html#8366" class="Function">≤-trans</a> <a id="17892" class="Symbol">(</a><a id="17893" href="plfa.part1.Relations.html#17430" class="Function">+-monoˡ-≤</a> <a id="17903" href="plfa.part1.Relations.html#17864" class="Bound">m</a> <a id="17905" href="plfa.part1.Relations.html#17866" class="Bound">n</a> <a id="17907" href="plfa.part1.Relations.html#17868" class="Bound">p</a> <a id="17909" href="plfa.part1.Relations.html#17872" class="Bound">m≤n</a><a id="17912" class="Symbol">)</a> <a id="17914" class="Symbol">(</a><a id="17915" href="plfa.part1.Relations.html#16630" class="Function">+-monoʳ-≤</a> <a id="17925" href="plfa.part1.Relations.html#17866" class="Bound">n</a> <a id="17927" href="plfa.part1.Relations.html#17868" class="Bound">p</a> <a id="17929" href="plfa.part1.Relations.html#17870" class="Bound">q</a> <a id="17931" href="plfa.part1.Relations.html#17876" class="Bound">p≤q</a><a id="17934" class="Symbol">)</a>
</pre>{% endraw %}Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

{% raw %}<pre class="Agda"><a id="18243" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
{% raw %}<pre class="Agda"><a id="18376" class="Keyword">infix</a> <a id="18382" class="Number">4</a> <a id="18384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18394" class="Datatype Operator">_&lt;_</a>

<a id="18389" class="Keyword">data</a> <a id="_&lt;_"></a><a id="18394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18394" class="Datatype Operator">_&lt;_</a> <a id="18398" class="Symbol">:</a> <a id="18400" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18402" class="Symbol">→</a> <a id="18404" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18406" class="Symbol">→</a> <a id="18408" class="PrimitiveType">Set</a> <a id="18412" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="18421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18421" class="InductiveConstructor">z&lt;s</a> <a id="18425" class="Symbol">:</a> <a id="18427" class="Symbol">∀</a> <a id="18429" class="Symbol">{</a><a id="18430" href="plfa.part1.Relations.html#18430" class="Bound">n</a> <a id="18432" class="Symbol">:</a> <a id="18434" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18435" class="Symbol">}</a>
      <a id="18443" class="Comment">------------</a>
    <a id="18460" class="Symbol">→</a> <a id="18462" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18394" class="Datatype Operator">&lt;</a> <a id="18469" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18473" href="plfa.part1.Relations.html#18430" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="18478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18478" class="InductiveConstructor">s&lt;s</a> <a id="18482" class="Symbol">:</a> <a id="18484" class="Symbol">∀</a> <a id="18486" class="Symbol">{</a><a id="18487" href="plfa.part1.Relations.html#18487" class="Bound">m</a> <a id="18489" href="plfa.part1.Relations.html#18489" class="Bound">n</a> <a id="18491" class="Symbol">:</a> <a id="18493" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18494" class="Symbol">}</a>
    <a id="18500" class="Symbol">→</a> <a id="18502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18487" class="Bound">m</a> <a id="18504" href="plfa.part1.Relations.html#18394" class="Datatype Operator">&lt;</a> <a id="18506" href="plfa.part1.Relations.html#18489" class="Bound">n</a>
      <a id="18514" class="Comment">-------------</a>
    <a id="18532" class="Symbol">→</a> <a id="18534" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18487" class="Bound">m</a> <a id="18540" href="plfa.part1.Relations.html#18394" class="Datatype Operator">&lt;</a> <a id="18542" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18546" href="plfa.part1.Relations.html#18489" class="Bound">n</a>
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

{% raw %}<pre class="Agda"><a id="19715" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `trichotomy` (practice) {#trichotomy}

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

{% raw %}<pre class="Agda"><a id="20214" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

{% raw %}<pre class="Agda"><a id="20434" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

{% raw %}<pre class="Agda"><a id="20577" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

{% raw %}<pre class="Agda"><a id="20848" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
{% raw %}<pre class="Agda"><a id="21087" class="Keyword">data</a> <a id="even"></a><a id="21092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21092" class="Datatype">even</a> <a id="21097" class="Symbol">:</a> <a id="21099" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21101" class="Symbol">→</a> <a id="21103" class="PrimitiveType">Set</a>
<a id="21107" class="Keyword">data</a> <a id="odd"></a><a id="21112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21112" class="Datatype">odd</a>  <a id="21117" class="Symbol">:</a> <a id="21119" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21121" class="Symbol">→</a> <a id="21123" class="PrimitiveType">Set</a>

<a id="21128" class="Keyword">data</a> <a id="21133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21092" class="Datatype">even</a> <a id="21138" class="Keyword">where</a>

  <a id="even.zero"></a><a id="21147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21147" class="InductiveConstructor">zero</a> <a id="21152" class="Symbol">:</a>
      <a id="21160" class="Comment">---------</a>
      <a id="21176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21092" class="Datatype">even</a> <a id="21181" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="21189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21189" class="InductiveConstructor">suc</a>  <a id="21194" class="Symbol">:</a> <a id="21196" class="Symbol">∀</a> <a id="21198" class="Symbol">{</a><a id="21199" href="plfa.part1.Relations.html#21199" class="Bound">n</a> <a id="21201" class="Symbol">:</a> <a id="21203" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21204" class="Symbol">}</a>
    <a id="21210" class="Symbol">→</a> <a id="21212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21112" class="Datatype">odd</a> <a id="21216" href="plfa.part1.Relations.html#21199" class="Bound">n</a>
      <a id="21224" class="Comment">------------</a>
    <a id="21241" class="Symbol">→</a> <a id="21243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21092" class="Datatype">even</a> <a id="21248" class="Symbol">(</a><a id="21249" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21253" href="plfa.part1.Relations.html#21199" class="Bound">n</a><a id="21254" class="Symbol">)</a>

<a id="21257" class="Keyword">data</a> <a id="21262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21112" class="Datatype">odd</a> <a id="21266" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="21275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21275" class="InductiveConstructor">suc</a>   <a id="21281" class="Symbol">:</a> <a id="21283" class="Symbol">∀</a> <a id="21285" class="Symbol">{</a><a id="21286" href="plfa.part1.Relations.html#21286" class="Bound">n</a> <a id="21288" class="Symbol">:</a> <a id="21290" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21291" class="Symbol">}</a>
    <a id="21297" class="Symbol">→</a> <a id="21299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21092" class="Datatype">even</a> <a id="21304" href="plfa.part1.Relations.html#21286" class="Bound">n</a>
      <a id="21312" class="Comment">-----------</a>
    <a id="21328" class="Symbol">→</a> <a id="21330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21112" class="Datatype">odd</a> <a id="21334" class="Symbol">(</a><a id="21335" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21339" href="plfa.part1.Relations.html#21286" class="Bound">n</a><a id="21340" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="e+e≡e"></a><a id="22500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22500" class="Function">e+e≡e</a> <a id="22506" class="Symbol">:</a> <a id="22508" class="Symbol">∀</a> <a id="22510" class="Symbol">{</a><a id="22511" href="plfa.part1.Relations.html#22511" class="Bound">m</a> <a id="22513" href="plfa.part1.Relations.html#22513" class="Bound">n</a> <a id="22515" class="Symbol">:</a> <a id="22517" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22518" class="Symbol">}</a>
  <a id="22522" class="Symbol">→</a> <a id="22524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21092" class="Datatype">even</a> <a id="22529" href="plfa.part1.Relations.html#22511" class="Bound">m</a>
  <a id="22533" class="Symbol">→</a> <a id="22535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21092" class="Datatype">even</a> <a id="22540" href="plfa.part1.Relations.html#22513" class="Bound">n</a>
    <a id="22546" class="Comment">------------</a>
  <a id="22561" class="Symbol">→</a> <a id="22563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21092" class="Datatype">even</a> <a id="22568" class="Symbol">(</a><a id="22569" href="plfa.part1.Relations.html#22511" class="Bound">m</a> <a id="22571" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22573" href="plfa.part1.Relations.html#22513" class="Bound">n</a><a id="22574" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="22577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22577" class="Function">o+e≡o</a> <a id="22583" class="Symbol">:</a> <a id="22585" class="Symbol">∀</a> <a id="22587" class="Symbol">{</a><a id="22588" href="plfa.part1.Relations.html#22588" class="Bound">m</a> <a id="22590" href="plfa.part1.Relations.html#22590" class="Bound">n</a> <a id="22592" class="Symbol">:</a> <a id="22594" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22595" class="Symbol">}</a>
  <a id="22599" class="Symbol">→</a> <a id="22601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21112" class="Datatype">odd</a> <a id="22605" href="plfa.part1.Relations.html#22588" class="Bound">m</a>
  <a id="22609" class="Symbol">→</a> <a id="22611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21092" class="Datatype">even</a> <a id="22616" href="plfa.part1.Relations.html#22590" class="Bound">n</a>
    <a id="22622" class="Comment">-----------</a>
  <a id="22636" class="Symbol">→</a> <a id="22638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21112" class="Datatype">odd</a> <a id="22642" class="Symbol">(</a><a id="22643" href="plfa.part1.Relations.html#22588" class="Bound">m</a> <a id="22645" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22647" href="plfa.part1.Relations.html#22590" class="Bound">n</a><a id="22648" class="Symbol">)</a>

<a id="22651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22500" class="Function">e+e≡e</a> <a id="22657" href="plfa.part1.Relations.html#21147" class="InductiveConstructor">zero</a>     <a id="22666" href="plfa.part1.Relations.html#22666" class="Bound">en</a>  <a id="22670" class="Symbol">=</a>  <a id="22673" href="plfa.part1.Relations.html#22666" class="Bound">en</a>
<a id="22676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22500" class="Function">e+e≡e</a> <a id="22682" class="Symbol">(</a><a id="22683" href="plfa.part1.Relations.html#21189" class="InductiveConstructor">suc</a> <a id="22687" href="plfa.part1.Relations.html#22687" class="Bound">om</a><a id="22689" class="Symbol">)</a> <a id="22691" href="plfa.part1.Relations.html#22691" class="Bound">en</a>  <a id="22695" class="Symbol">=</a>  <a id="22698" href="plfa.part1.Relations.html#21189" class="InductiveConstructor">suc</a> <a id="22702" class="Symbol">(</a><a id="22703" href="plfa.part1.Relations.html#22577" class="Function">o+e≡o</a> <a id="22709" href="plfa.part1.Relations.html#22687" class="Bound">om</a> <a id="22712" href="plfa.part1.Relations.html#22691" class="Bound">en</a><a id="22714" class="Symbol">)</a>

<a id="22717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22577" class="Function">o+e≡o</a> <a id="22723" class="Symbol">(</a><a id="22724" href="plfa.part1.Relations.html#21275" class="InductiveConstructor">suc</a> <a id="22728" href="plfa.part1.Relations.html#22728" class="Bound">em</a><a id="22730" class="Symbol">)</a> <a id="22732" href="plfa.part1.Relations.html#22732" class="Bound">en</a>  <a id="22736" class="Symbol">=</a>  <a id="22739" href="plfa.part1.Relations.html#21275" class="InductiveConstructor">suc</a> <a id="22743" class="Symbol">(</a><a id="22744" href="plfa.part1.Relations.html#22500" class="Function">e+e≡e</a> <a id="22750" href="plfa.part1.Relations.html#22728" class="Bound">em</a> <a id="22753" href="plfa.part1.Relations.html#22732" class="Bound">en</a><a id="22755" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="23893" class="Comment">-- Your code goes here</a>
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

{% raw %}<pre class="Agda"><a id="25185" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="25321" class="Keyword">import</a> <a id="25328" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="25337" class="Keyword">using</a> <a id="25343" class="Symbol">(</a><a id="25344" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="25347" class="Symbol">;</a> <a id="25349" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="25352" class="Symbol">;</a> <a id="25354" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="25357" class="Symbol">)</a>
<a id="25359" class="Keyword">import</a> <a id="25366" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="25386" class="Keyword">using</a> <a id="25392" class="Symbol">(</a><a id="25393" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="25399" class="Symbol">;</a> <a id="25401" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="25408" class="Symbol">;</a> <a id="25410" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="25419" class="Symbol">;</a> <a id="25421" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="25428" class="Symbol">;</a>
                                  <a id="25464" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="25473" class="Symbol">;</a> <a id="25475" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="25484" class="Symbol">;</a> <a id="25486" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="25494" class="Symbol">)</a>
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
