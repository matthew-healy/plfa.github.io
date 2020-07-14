---
src       : "src/plfa/part1/Equality.lagda.md"
title     : "Equality: Equality and equational reasoning"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
---

{% raw %}<pre class="Agda"><a id="162" class="Keyword">module</a> <a id="169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}" class="Module">plfa.part1.Equality</a> <a id="189" class="Keyword">where</a>
</pre>{% endraw %}
Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.


## Equality

We declare equality as follows:
{% raw %}<pre class="Agda"><a id="725" class="Keyword">data</a> <a id="_≡_"></a><a id="730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">_≡_</a> <a id="734" class="Symbol">{</a><a id="735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#735" class="Bound">A</a> <a id="737" class="Symbol">:</a> <a id="739" class="PrimitiveType">Set</a><a id="742" class="Symbol">}</a> <a id="744" class="Symbol">(</a><a id="745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#745" class="Bound">x</a> <a id="747" class="Symbol">:</a> <a id="749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#735" class="Bound">A</a><a id="750" class="Symbol">)</a> <a id="752" class="Symbol">:</a> <a id="754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#735" class="Bound">A</a> <a id="756" class="Symbol">→</a> <a id="758" class="PrimitiveType">Set</a> <a id="762" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a> <a id="775" class="Symbol">:</a> <a id="777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#745" class="Bound">x</a> <a id="779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#745" class="Bound">x</a>
</pre>{% endraw %}In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.

We declare the precedence of equality as follows:
{% raw %}<pre class="Agda"><a id="1430" class="Keyword">infix</a> <a id="1436" class="Number">4</a> <a id="1438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">_≡_</a>
</pre>{% endraw %}We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equality is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry:
{% raw %}<pre class="Agda"><a id="sym"></a><a id="1893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1893" class="Function">sym</a> <a id="1897" class="Symbol">:</a> <a id="1899" class="Symbol">∀</a> <a id="1901" class="Symbol">{</a><a id="1902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1902" class="Bound">A</a> <a id="1904" class="Symbol">:</a> <a id="1906" class="PrimitiveType">Set</a><a id="1909" class="Symbol">}</a> <a id="1911" class="Symbol">{</a><a id="1912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1912" class="Bound">x</a> <a id="1914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1914" class="Bound">y</a> <a id="1916" class="Symbol">:</a> <a id="1918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1902" class="Bound">A</a><a id="1919" class="Symbol">}</a>
  <a id="1923" class="Symbol">→</a> <a id="1925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1912" class="Bound">x</a> <a id="1927" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="1929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1914" class="Bound">y</a>
    <a id="1935" class="Comment">-----</a>
  <a id="1943" class="Symbol">→</a> <a id="1945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1914" class="Bound">y</a> <a id="1947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="1949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1912" class="Bound">x</a>
<a id="1951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#1893" class="Function">sym</a> <a id="1955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a> <a id="1960" class="Symbol">=</a> <a id="1962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>
</pre>{% endraw %}How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.

It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward:
{% raw %}<pre class="Agda"><a id="trans"></a><a id="3621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3621" class="Function">trans</a> <a id="3627" class="Symbol">:</a> <a id="3629" class="Symbol">∀</a> <a id="3631" class="Symbol">{</a><a id="3632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3632" class="Bound">A</a> <a id="3634" class="Symbol">:</a> <a id="3636" class="PrimitiveType">Set</a><a id="3639" class="Symbol">}</a> <a id="3641" class="Symbol">{</a><a id="3642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3642" class="Bound">x</a> <a id="3644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3644" class="Bound">y</a> <a id="3646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3646" class="Bound">z</a> <a id="3648" class="Symbol">:</a> <a id="3650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3632" class="Bound">A</a><a id="3651" class="Symbol">}</a>
  <a id="3655" class="Symbol">→</a> <a id="3657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3642" class="Bound">x</a> <a id="3659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="3661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3644" class="Bound">y</a>
  <a id="3665" class="Symbol">→</a> <a id="3667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3644" class="Bound">y</a> <a id="3669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="3671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3646" class="Bound">z</a>
    <a id="3677" class="Comment">-----</a>
  <a id="3685" class="Symbol">→</a> <a id="3687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3642" class="Bound">x</a> <a id="3689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="3691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3646" class="Bound">z</a>
<a id="3693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3621" class="Function">trans</a> <a id="3699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a> <a id="3704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>  <a id="3710" class="Symbol">=</a>  <a id="3713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>
</pre>{% endraw %}Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.

## Congruence and substitution {#cong}

Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both:
{% raw %}<pre class="Agda"><a id="cong"></a><a id="4037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4037" class="Function">cong</a> <a id="4042" class="Symbol">:</a> <a id="4044" class="Symbol">∀</a> <a id="4046" class="Symbol">{</a><a id="4047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4047" class="Bound">A</a> <a id="4049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4049" class="Bound">B</a> <a id="4051" class="Symbol">:</a> <a id="4053" class="PrimitiveType">Set</a><a id="4056" class="Symbol">}</a> <a id="4058" class="Symbol">(</a><a id="4059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4059" class="Bound">f</a> <a id="4061" class="Symbol">:</a> <a id="4063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4047" class="Bound">A</a> <a id="4065" class="Symbol">→</a> <a id="4067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4049" class="Bound">B</a><a id="4068" class="Symbol">)</a> <a id="4070" class="Symbol">{</a><a id="4071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4071" class="Bound">x</a> <a id="4073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4073" class="Bound">y</a> <a id="4075" class="Symbol">:</a> <a id="4077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4047" class="Bound">A</a><a id="4078" class="Symbol">}</a>
  <a id="4082" class="Symbol">→</a> <a id="4084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4071" class="Bound">x</a> <a id="4086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="4088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4073" class="Bound">y</a>
    <a id="4094" class="Comment">---------</a>
  <a id="4106" class="Symbol">→</a> <a id="4108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4059" class="Bound">f</a> <a id="4110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4071" class="Bound">x</a> <a id="4112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="4114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4059" class="Bound">f</a> <a id="4116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4073" class="Bound">y</a>
<a id="4118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4037" class="Function">cong</a> <a id="4123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4123" class="Bound">f</a> <a id="4125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>  <a id="4131" class="Symbol">=</a>  <a id="4134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
Congruence of functions with two arguments is similar:
{% raw %}<pre class="Agda"><a id="cong₂"></a><a id="4203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4203" class="Function">cong₂</a> <a id="4209" class="Symbol">:</a> <a id="4211" class="Symbol">∀</a> <a id="4213" class="Symbol">{</a><a id="4214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4214" class="Bound">A</a> <a id="4216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4216" class="Bound">B</a> <a id="4218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4218" class="Bound">C</a> <a id="4220" class="Symbol">:</a> <a id="4222" class="PrimitiveType">Set</a><a id="4225" class="Symbol">}</a> <a id="4227" class="Symbol">(</a><a id="4228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4228" class="Bound">f</a> <a id="4230" class="Symbol">:</a> <a id="4232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4214" class="Bound">A</a> <a id="4234" class="Symbol">→</a> <a id="4236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4216" class="Bound">B</a> <a id="4238" class="Symbol">→</a> <a id="4240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4218" class="Bound">C</a><a id="4241" class="Symbol">)</a> <a id="4243" class="Symbol">{</a><a id="4244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4244" class="Bound">u</a> <a id="4246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4246" class="Bound">x</a> <a id="4248" class="Symbol">:</a> <a id="4250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4214" class="Bound">A</a><a id="4251" class="Symbol">}</a> <a id="4253" class="Symbol">{</a><a id="4254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4254" class="Bound">v</a> <a id="4256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4256" class="Bound">y</a> <a id="4258" class="Symbol">:</a> <a id="4260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4216" class="Bound">B</a><a id="4261" class="Symbol">}</a>
  <a id="4265" class="Symbol">→</a> <a id="4267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4244" class="Bound">u</a> <a id="4269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="4271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4246" class="Bound">x</a>
  <a id="4275" class="Symbol">→</a> <a id="4277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4254" class="Bound">v</a> <a id="4279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="4281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4256" class="Bound">y</a>
    <a id="4287" class="Comment">-------------</a>
  <a id="4303" class="Symbol">→</a> <a id="4305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4228" class="Bound">f</a> <a id="4307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4244" class="Bound">u</a> <a id="4309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4254" class="Bound">v</a> <a id="4311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="4313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4228" class="Bound">f</a> <a id="4315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4246" class="Bound">x</a> <a id="4317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4256" class="Bound">y</a>
<a id="4319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4203" class="Function">cong₂</a> <a id="4325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4325" class="Bound">f</a> <a id="4327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a> <a id="4332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>  <a id="4338" class="Symbol">=</a>  <a id="4341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms:
{% raw %}<pre class="Agda"><a id="cong-app"></a><a id="4513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4513" class="Function">cong-app</a> <a id="4522" class="Symbol">:</a> <a id="4524" class="Symbol">∀</a> <a id="4526" class="Symbol">{</a><a id="4527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4527" class="Bound">A</a> <a id="4529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4529" class="Bound">B</a> <a id="4531" class="Symbol">:</a> <a id="4533" class="PrimitiveType">Set</a><a id="4536" class="Symbol">}</a> <a id="4538" class="Symbol">{</a><a id="4539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4539" class="Bound">f</a> <a id="4541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4541" class="Bound">g</a> <a id="4543" class="Symbol">:</a> <a id="4545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4527" class="Bound">A</a> <a id="4547" class="Symbol">→</a> <a id="4549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4529" class="Bound">B</a><a id="4550" class="Symbol">}</a>
  <a id="4554" class="Symbol">→</a> <a id="4556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4539" class="Bound">f</a> <a id="4558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="4560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4541" class="Bound">g</a>
    <a id="4566" class="Comment">---------------------</a>
  <a id="4590" class="Symbol">→</a> <a id="4592" class="Symbol">∀</a> <a id="4594" class="Symbol">(</a><a id="4595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4595" class="Bound">x</a> <a id="4597" class="Symbol">:</a> <a id="4599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4527" class="Bound">A</a><a id="4600" class="Symbol">)</a> <a id="4602" class="Symbol">→</a> <a id="4604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4539" class="Bound">f</a> <a id="4606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4595" class="Bound">x</a> <a id="4608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="4610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4541" class="Bound">g</a> <a id="4612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4595" class="Bound">x</a>
<a id="4614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4513" class="Function">cong-app</a> <a id="4623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a> <a id="4628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4628" class="Bound">x</a> <a id="4630" class="Symbol">=</a> <a id="4632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second:
{% raw %}<pre class="Agda"><a id="subst"></a><a id="4779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4779" class="Function">subst</a> <a id="4785" class="Symbol">:</a> <a id="4787" class="Symbol">∀</a> <a id="4789" class="Symbol">{</a><a id="4790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4790" class="Bound">A</a> <a id="4792" class="Symbol">:</a> <a id="4794" class="PrimitiveType">Set</a><a id="4797" class="Symbol">}</a> <a id="4799" class="Symbol">{</a><a id="4800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4800" class="Bound">x</a> <a id="4802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4802" class="Bound">y</a> <a id="4804" class="Symbol">:</a> <a id="4806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4790" class="Bound">A</a><a id="4807" class="Symbol">}</a> <a id="4809" class="Symbol">(</a><a id="4810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4810" class="Bound">P</a> <a id="4812" class="Symbol">:</a> <a id="4814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4790" class="Bound">A</a> <a id="4816" class="Symbol">→</a> <a id="4818" class="PrimitiveType">Set</a><a id="4821" class="Symbol">)</a>
  <a id="4825" class="Symbol">→</a> <a id="4827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4800" class="Bound">x</a> <a id="4829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="4831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4802" class="Bound">y</a>
    <a id="4837" class="Comment">---------</a>
  <a id="4849" class="Symbol">→</a> <a id="4851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4810" class="Bound">P</a> <a id="4853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4800" class="Bound">x</a> <a id="4855" class="Symbol">→</a> <a id="4857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4810" class="Bound">P</a> <a id="4859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4802" class="Bound">y</a>
<a id="4861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4779" class="Function">subst</a> <a id="4867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4867" class="Bound">P</a> <a id="4869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a> <a id="4874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4874" class="Bound">px</a> <a id="4877" class="Symbol">=</a> <a id="4879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4874" class="Bound">px</a>
</pre>{% endraw %}

## Chains of equations

Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library:
{% raw %}<pre class="Agda"><a id="5127" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="5134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5134" class="Module">≡-Reasoning</a> <a id="5146" class="Symbol">{</a><a id="5147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5147" class="Bound">A</a> <a id="5149" class="Symbol">:</a> <a id="5151" class="PrimitiveType">Set</a><a id="5154" class="Symbol">}</a> <a id="5156" class="Keyword">where</a>

  <a id="5165" class="Keyword">infix</a>  <a id="5172" class="Number">1</a> <a id="5174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5222" class="Function Operator">begin_</a>
  <a id="5183" class="Keyword">infixr</a> <a id="5190" class="Number">2</a> <a id="5192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5302" class="Function Operator">_≡⟨⟩_</a> <a id="5198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">_≡⟨_⟩_</a>
  <a id="5207" class="Keyword">infix</a>  <a id="5214" class="Number">3</a> <a id="5216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5502" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="5222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5222" class="Function Operator">begin_</a> <a id="5229" class="Symbol">:</a> <a id="5231" class="Symbol">∀</a> <a id="5233" class="Symbol">{</a><a id="5234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5234" class="Bound">x</a> <a id="5236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5236" class="Bound">y</a> <a id="5238" class="Symbol">:</a> <a id="5240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5147" class="Bound">A</a><a id="5241" class="Symbol">}</a>
    <a id="5247" class="Symbol">→</a> <a id="5249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5234" class="Bound">x</a> <a id="5251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="5253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5236" class="Bound">y</a>
      <a id="5261" class="Comment">-----</a>
    <a id="5271" class="Symbol">→</a> <a id="5273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5234" class="Bound">x</a> <a id="5275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="5277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5236" class="Bound">y</a>
  <a id="5281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5222" class="Function Operator">begin</a> <a id="5287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5287" class="Bound">x≡y</a>  <a id="5292" class="Symbol">=</a>  <a id="5295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5287" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="5302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5302" class="Function Operator">_≡⟨⟩_</a> <a id="5308" class="Symbol">:</a> <a id="5310" class="Symbol">∀</a> <a id="5312" class="Symbol">(</a><a id="5313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5313" class="Bound">x</a> <a id="5315" class="Symbol">:</a> <a id="5317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5147" class="Bound">A</a><a id="5318" class="Symbol">)</a> <a id="5320" class="Symbol">{</a><a id="5321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5321" class="Bound">y</a> <a id="5323" class="Symbol">:</a> <a id="5325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5147" class="Bound">A</a><a id="5326" class="Symbol">}</a>
    <a id="5332" class="Symbol">→</a> <a id="5334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5313" class="Bound">x</a> <a id="5336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="5338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5321" class="Bound">y</a>
      <a id="5346" class="Comment">-----</a>
    <a id="5356" class="Symbol">→</a> <a id="5358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5313" class="Bound">x</a> <a id="5360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="5362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5321" class="Bound">y</a>
  <a id="5366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5366" class="Bound">x</a> <a id="5368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5302" class="Function Operator">≡⟨⟩</a> <a id="5372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5372" class="Bound">x≡y</a>  <a id="5377" class="Symbol">=</a>  <a id="5380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5372" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="5387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">_≡⟨_⟩_</a> <a id="5394" class="Symbol">:</a> <a id="5396" class="Symbol">∀</a> <a id="5398" class="Symbol">(</a><a id="5399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5399" class="Bound">x</a> <a id="5401" class="Symbol">:</a> <a id="5403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5147" class="Bound">A</a><a id="5404" class="Symbol">)</a> <a id="5406" class="Symbol">{</a><a id="5407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5407" class="Bound">y</a> <a id="5409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5409" class="Bound">z</a> <a id="5411" class="Symbol">:</a> <a id="5413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5147" class="Bound">A</a><a id="5414" class="Symbol">}</a>
    <a id="5420" class="Symbol">→</a> <a id="5422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5399" class="Bound">x</a> <a id="5424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="5426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5407" class="Bound">y</a>
    <a id="5432" class="Symbol">→</a> <a id="5434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5407" class="Bound">y</a> <a id="5436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="5438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5409" class="Bound">z</a>
      <a id="5446" class="Comment">-----</a>
    <a id="5456" class="Symbol">→</a> <a id="5458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5399" class="Bound">x</a> <a id="5460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="5462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5409" class="Bound">z</a>
  <a id="5466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5466" class="Bound">x</a> <a id="5468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">≡⟨</a> <a id="5471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5471" class="Bound">x≡y</a> <a id="5475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">⟩</a> <a id="5477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5477" class="Bound">y≡z</a>  <a id="5482" class="Symbol">=</a>  <a id="5485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#3621" class="Function">trans</a> <a id="5491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5471" class="Bound">x≡y</a> <a id="5495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5477" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="5502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5502" class="Function Operator">_∎</a> <a id="5505" class="Symbol">:</a> <a id="5507" class="Symbol">∀</a> <a id="5509" class="Symbol">(</a><a id="5510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5510" class="Bound">x</a> <a id="5512" class="Symbol">:</a> <a id="5514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5147" class="Bound">A</a><a id="5515" class="Symbol">)</a>
      <a id="5523" class="Comment">-----</a>
    <a id="5533" class="Symbol">→</a> <a id="5535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5510" class="Bound">x</a> <a id="5537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="5539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5510" class="Bound">x</a>
  <a id="5543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5543" class="Bound">x</a> <a id="5545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5502" class="Function Operator">∎</a>  <a id="5548" class="Symbol">=</a>  <a id="5551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>

<a id="5557" class="Keyword">open</a> <a id="5562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5134" class="Module">≡-Reasoning</a>
</pre>{% endraw %}This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.

As an example, let's look at a proof of transitivity
as a chain of equations:
{% raw %}<pre class="Agda"><a id="trans′"></a><a id="6193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6193" class="Function">trans′</a> <a id="6200" class="Symbol">:</a> <a id="6202" class="Symbol">∀</a> <a id="6204" class="Symbol">{</a><a id="6205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6205" class="Bound">A</a> <a id="6207" class="Symbol">:</a> <a id="6209" class="PrimitiveType">Set</a><a id="6212" class="Symbol">}</a> <a id="6214" class="Symbol">{</a><a id="6215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6215" class="Bound">x</a> <a id="6217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6217" class="Bound">y</a> <a id="6219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6219" class="Bound">z</a> <a id="6221" class="Symbol">:</a> <a id="6223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6205" class="Bound">A</a><a id="6224" class="Symbol">}</a>
  <a id="6228" class="Symbol">→</a> <a id="6230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6215" class="Bound">x</a> <a id="6232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="6234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6217" class="Bound">y</a>
  <a id="6238" class="Symbol">→</a> <a id="6240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6217" class="Bound">y</a> <a id="6242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="6244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6219" class="Bound">z</a>
    <a id="6250" class="Comment">-----</a>
  <a id="6258" class="Symbol">→</a> <a id="6260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6215" class="Bound">x</a> <a id="6262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="6264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6219" class="Bound">z</a>
<a id="6266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6193" class="Function">trans′</a> <a id="6273" class="Symbol">{</a><a id="6274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6274" class="Bound">A</a><a id="6275" class="Symbol">}</a> <a id="6277" class="Symbol">{</a><a id="6278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6278" class="Bound">x</a><a id="6279" class="Symbol">}</a> <a id="6281" class="Symbol">{</a><a id="6282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6282" class="Bound">y</a><a id="6283" class="Symbol">}</a> <a id="6285" class="Symbol">{</a><a id="6286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6286" class="Bound">z</a><a id="6287" class="Symbol">}</a> <a id="6289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6289" class="Bound">x≡y</a> <a id="6293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6293" class="Bound">y≡z</a> <a id="6297" class="Symbol">=</a>
  <a id="6301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5222" class="Function Operator">begin</a>
    <a id="6311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6278" class="Bound">x</a>
  <a id="6315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">≡⟨</a> <a id="6318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6289" class="Bound">x≡y</a> <a id="6322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">⟩</a>
    <a id="6328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6282" class="Bound">y</a>
  <a id="6332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">≡⟨</a> <a id="6335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6293" class="Bound">y≡z</a> <a id="6339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">⟩</a>
    <a id="6345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#6286" class="Bound">z</a>
  <a id="6349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5502" class="Function Operator">∎</a>
</pre>{% endraw %}According to the fixity declarations, the body parses as follows:

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:

    trans x≡y (trans y≡z refl)

We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` that ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.


## Chains of equations, another example

As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict:
{% raw %}<pre class="Agda"><a id="8034" class="Keyword">data</a> <a id="ℕ"></a><a id="8039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a> <a id="8041" class="Symbol">:</a> <a id="8043" class="PrimitiveType">Set</a> <a id="8047" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="8055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8055" class="InductiveConstructor">zero</a> <a id="8060" class="Symbol">:</a> <a id="8062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="8066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a>  <a id="8071" class="Symbol">:</a> <a id="8073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a> <a id="8075" class="Symbol">→</a> <a id="8077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="8080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">_+_</a> <a id="8084" class="Symbol">:</a> <a id="8086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a> <a id="8088" class="Symbol">→</a> <a id="8090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a> <a id="8092" class="Symbol">→</a> <a id="8094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a>
<a id="8096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8055" class="InductiveConstructor">zero</a>    <a id="8104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8106" class="Bound">n</a>  <a id="8109" class="Symbol">=</a>  <a id="8112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8106" class="Bound">n</a>
<a id="8114" class="Symbol">(</a><a id="8115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8119" class="Bound">m</a><a id="8120" class="Symbol">)</a> <a id="8122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8124" class="Bound">n</a>  <a id="8127" class="Symbol">=</a>  <a id="8130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8134" class="Symbol">(</a><a id="8135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8119" class="Bound">m</a> <a id="8137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8124" class="Bound">n</a><a id="8140" class="Symbol">)</a>
</pre>{% endraw %}
To save space we postulate (rather than prove in full) two lemmas:
{% raw %}<pre class="Agda"><a id="8218" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="8230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8230" class="Postulate">+-identity</a> <a id="8241" class="Symbol">:</a> <a id="8243" class="Symbol">∀</a> <a id="8245" class="Symbol">(</a><a id="8246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8246" class="Bound">m</a> <a id="8248" class="Symbol">:</a> <a id="8250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a><a id="8251" class="Symbol">)</a> <a id="8253" class="Symbol">→</a> <a id="8255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8246" class="Bound">m</a> <a id="8257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8055" class="InductiveConstructor">zero</a> <a id="8264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="8266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8246" class="Bound">m</a>
  <a id="+-suc"></a><a id="8270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8270" class="Postulate">+-suc</a> <a id="8276" class="Symbol">:</a> <a id="8278" class="Symbol">∀</a> <a id="8280" class="Symbol">(</a><a id="8281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8281" class="Bound">m</a> <a id="8283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8283" class="Bound">n</a> <a id="8285" class="Symbol">:</a> <a id="8287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a><a id="8288" class="Symbol">)</a> <a id="8290" class="Symbol">→</a> <a id="8292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8281" class="Bound">m</a> <a id="8294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8283" class="Bound">n</a> <a id="8302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="8304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8308" class="Symbol">(</a><a id="8309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8281" class="Bound">m</a> <a id="8311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8283" class="Bound">n</a><a id="8314" class="Symbol">)</a>
</pre>{% endraw %}This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.

We then repeat the proof of commutativity:
{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="8664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8664" class="Function">+-comm</a> <a id="8671" class="Symbol">:</a> <a id="8673" class="Symbol">∀</a> <a id="8675" class="Symbol">(</a><a id="8676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8676" class="Bound">m</a> <a id="8678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8678" class="Bound">n</a> <a id="8680" class="Symbol">:</a> <a id="8682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a><a id="8683" class="Symbol">)</a> <a id="8685" class="Symbol">→</a> <a id="8687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8676" class="Bound">m</a> <a id="8689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8678" class="Bound">n</a> <a id="8693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="8695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8678" class="Bound">n</a> <a id="8697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8676" class="Bound">m</a>
<a id="8701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8664" class="Function">+-comm</a> <a id="8708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8708" class="Bound">m</a> <a id="8710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8055" class="InductiveConstructor">zero</a> <a id="8715" class="Symbol">=</a>
  <a id="8719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5222" class="Function Operator">begin</a>
    <a id="8729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8708" class="Bound">m</a> <a id="8731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8055" class="InductiveConstructor">zero</a>
  <a id="8740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">≡⟨</a> <a id="8743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8230" class="Postulate">+-identity</a> <a id="8754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8708" class="Bound">m</a> <a id="8756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">⟩</a>
    <a id="8762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8708" class="Bound">m</a>
  <a id="8766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5302" class="Function Operator">≡⟨⟩</a>
    <a id="8774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8055" class="InductiveConstructor">zero</a> <a id="8779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8708" class="Bound">m</a>
  <a id="8785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5502" class="Function Operator">∎</a>
<a id="8787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8664" class="Function">+-comm</a> <a id="8794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8794" class="Bound">m</a> <a id="8796" class="Symbol">(</a><a id="8797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8801" class="Bound">n</a><a id="8802" class="Symbol">)</a> <a id="8804" class="Symbol">=</a>
  <a id="8808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5222" class="Function Operator">begin</a>
    <a id="8818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8794" class="Bound">m</a> <a id="8820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8826" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8801" class="Bound">n</a>
  <a id="8830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">≡⟨</a> <a id="8833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8270" class="Postulate">+-suc</a> <a id="8839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8794" class="Bound">m</a> <a id="8841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8801" class="Bound">n</a> <a id="8843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">⟩</a>
    <a id="8849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8853" class="Symbol">(</a><a id="8854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8794" class="Bound">m</a> <a id="8856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8801" class="Bound">n</a><a id="8859" class="Symbol">)</a>
  <a id="8863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">≡⟨</a> <a id="8866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4037" class="Function">cong</a> <a id="8871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8875" class="Symbol">(</a><a id="8876" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8664" class="Function">+-comm</a> <a id="8883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8794" class="Bound">m</a> <a id="8885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8801" class="Bound">n</a><a id="8886" class="Symbol">)</a> <a id="8888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5387" class="Function Operator">⟩</a>
    <a id="8894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8898" class="Symbol">(</a><a id="8899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8801" class="Bound">n</a> <a id="8901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8794" class="Bound">m</a><a id="8904" class="Symbol">)</a>
  <a id="8908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5302" class="Function Operator">≡⟨⟩</a>
    <a id="8916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="8920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8801" class="Bound">n</a> <a id="8922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="8924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8794" class="Bound">m</a>
  <a id="8928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#5502" class="Function Operator">∎</a>
</pre>{% endraw %}The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.

Agda always treats a term as equivalent to its
simplified term.  The reason that one can write

      suc (n + m)
    ≡⟨⟩
      suc n + m

is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write

      suc n + m
    ≡⟨⟩
      suc (n + m)

and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.


#### Exercise `≤-Reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}/Relations/)
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.

{% raw %}<pre class="Agda"><a id="10008" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}


## Rewriting

Consider a property of natural numbers, such as being even.
We repeat the earlier definition:
{% raw %}<pre class="Agda"><a id="10150" class="Keyword">data</a> <a id="even"></a><a id="10155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="10160" class="Symbol">:</a> <a id="10162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a> <a id="10164" class="Symbol">→</a> <a id="10166" class="PrimitiveType">Set</a>
<a id="10170" class="Keyword">data</a> <a id="odd"></a><a id="10175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10175" class="Datatype">odd</a>  <a id="10180" class="Symbol">:</a> <a id="10182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a> <a id="10184" class="Symbol">→</a> <a id="10186" class="PrimitiveType">Set</a>

<a id="10191" class="Keyword">data</a> <a id="10196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="10201" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="10210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10210" class="InductiveConstructor">even-zero</a> <a id="10220" class="Symbol">:</a> <a id="10222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="10227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8055" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="10235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10235" class="InductiveConstructor">even-suc</a> <a id="10244" class="Symbol">:</a> <a id="10246" class="Symbol">∀</a> <a id="10248" class="Symbol">{</a><a id="10249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10249" class="Bound">n</a> <a id="10251" class="Symbol">:</a> <a id="10253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a><a id="10254" class="Symbol">}</a>
    <a id="10260" class="Symbol">→</a> <a id="10262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10175" class="Datatype">odd</a> <a id="10266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10249" class="Bound">n</a>
      <a id="10274" class="Comment">------------</a>
    <a id="10291" class="Symbol">→</a> <a id="10293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="10298" class="Symbol">(</a><a id="10299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="10303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10249" class="Bound">n</a><a id="10304" class="Symbol">)</a>

<a id="10307" class="Keyword">data</a> <a id="10312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10175" class="Datatype">odd</a> <a id="10316" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="10324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10324" class="InductiveConstructor">odd-suc</a> <a id="10332" class="Symbol">:</a> <a id="10334" class="Symbol">∀</a> <a id="10336" class="Symbol">{</a><a id="10337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10337" class="Bound">n</a> <a id="10339" class="Symbol">:</a> <a id="10341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a><a id="10342" class="Symbol">}</a>
    <a id="10348" class="Symbol">→</a> <a id="10350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="10355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10337" class="Bound">n</a>
      <a id="10363" class="Comment">-----------</a>
    <a id="10379" class="Symbol">→</a> <a id="10381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10175" class="Datatype">odd</a> <a id="10385" class="Symbol">(</a><a id="10386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="10390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10337" class="Bound">n</a><a id="10391" class="Symbol">)</a>
</pre>{% endraw %}In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.

Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality:
{% raw %}<pre class="Agda"><a id="10789" class="Symbol">{-#</a> <a id="10793" class="Keyword">BUILTIN</a> <a id="10801" class="Pragma">EQUALITY</a> <a id="10810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">_≡_</a> <a id="10814" class="Symbol">#-}</a>
</pre>{% endraw %}
We can then prove the desired property as follows:
{% raw %}<pre class="Agda"><a id="even-comm"></a><a id="10878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10878" class="Function">even-comm</a> <a id="10888" class="Symbol">:</a> <a id="10890" class="Symbol">∀</a> <a id="10892" class="Symbol">(</a><a id="10893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10893" class="Bound">m</a> <a id="10895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10895" class="Bound">n</a> <a id="10897" class="Symbol">:</a> <a id="10899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a><a id="10900" class="Symbol">)</a>
  <a id="10904" class="Symbol">→</a> <a id="10906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="10911" class="Symbol">(</a><a id="10912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10893" class="Bound">m</a> <a id="10914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="10916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10895" class="Bound">n</a><a id="10917" class="Symbol">)</a>
    <a id="10923" class="Comment">------------</a>
  <a id="10938" class="Symbol">→</a> <a id="10940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="10945" class="Symbol">(</a><a id="10946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10895" class="Bound">n</a> <a id="10948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="10950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10893" class="Bound">m</a><a id="10951" class="Symbol">)</a>
<a id="10953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10878" class="Function">even-comm</a> <a id="10963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10963" class="Bound">m</a> <a id="10965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10965" class="Bound">n</a> <a id="10967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10967" class="Bound">ev</a>  <a id="10971" class="Keyword">rewrite</a> <a id="10979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8664" class="Function">+-comm</a> <a id="10986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10965" class="Bound">n</a> <a id="10988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10963" class="Bound">m</a>  <a id="10991" class="Symbol">=</a>  <a id="10994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10967" class="Bound">ev</a>
</pre>{% endraw %}Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.

It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

Now we add the rewrite:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.


## Multiple rewrites

One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities:
{% raw %}<pre class="Agda"><a id="+-comm′"></a><a id="12654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12654" class="Function">+-comm′</a> <a id="12662" class="Symbol">:</a> <a id="12664" class="Symbol">∀</a> <a id="12666" class="Symbol">(</a><a id="12667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12667" class="Bound">m</a> <a id="12669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12669" class="Bound">n</a> <a id="12671" class="Symbol">:</a> <a id="12673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a><a id="12674" class="Symbol">)</a> <a id="12676" class="Symbol">→</a> <a id="12678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12667" class="Bound">m</a> <a id="12680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="12682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12669" class="Bound">n</a> <a id="12684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="12686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12669" class="Bound">n</a> <a id="12688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="12690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12667" class="Bound">m</a>
<a id="12692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12654" class="Function">+-comm′</a> <a id="12700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8055" class="InductiveConstructor">zero</a>    <a id="12708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12708" class="Bound">n</a>  <a id="12711" class="Keyword">rewrite</a> <a id="12719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8230" class="Postulate">+-identity</a> <a id="12730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12708" class="Bound">n</a>             <a id="12744" class="Symbol">=</a>  <a id="12747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>
<a id="12752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12654" class="Function">+-comm′</a> <a id="12760" class="Symbol">(</a><a id="12761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8066" class="InductiveConstructor">suc</a> <a id="12765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12765" class="Bound">m</a><a id="12766" class="Symbol">)</a> <a id="12768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12768" class="Bound">n</a>  <a id="12771" class="Keyword">rewrite</a> <a id="12779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8270" class="Postulate">+-suc</a> <a id="12785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12768" class="Bound">n</a> <a id="12787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12765" class="Bound">m</a> <a id="12789" class="Symbol">|</a> <a id="12791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12654" class="Function">+-comm′</a> <a id="12799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12765" class="Bound">m</a> <a id="12801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#12768" class="Bound">n</a>  <a id="12804" class="Symbol">=</a>  <a id="12807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>
</pre>{% endraw %}This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.


## Rewriting expanded

The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction:
{% raw %}<pre class="Agda"><a id="even-comm′"></a><a id="13356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13356" class="Function">even-comm′</a> <a id="13367" class="Symbol">:</a> <a id="13369" class="Symbol">∀</a> <a id="13371" class="Symbol">(</a><a id="13372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13372" class="Bound">m</a> <a id="13374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13374" class="Bound">n</a> <a id="13376" class="Symbol">:</a> <a id="13378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a><a id="13379" class="Symbol">)</a>
  <a id="13383" class="Symbol">→</a> <a id="13385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="13390" class="Symbol">(</a><a id="13391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13372" class="Bound">m</a> <a id="13393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="13395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13374" class="Bound">n</a><a id="13396" class="Symbol">)</a>
    <a id="13402" class="Comment">------------</a>
  <a id="13417" class="Symbol">→</a> <a id="13419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="13424" class="Symbol">(</a><a id="13425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13374" class="Bound">n</a> <a id="13427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="13429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13372" class="Bound">m</a><a id="13430" class="Symbol">)</a>
<a id="13432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13356" class="Function">even-comm′</a> <a id="13443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13443" class="Bound">m</a> <a id="13445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13445" class="Bound">n</a> <a id="13447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13447" class="Bound">ev</a> <a id="13450" class="Keyword">with</a>   <a id="13457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13443" class="Bound">m</a> <a id="13459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="13461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13445" class="Bound">n</a>  <a id="13464" class="Symbol">|</a> <a id="13466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8664" class="Function">+-comm</a> <a id="13473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13443" class="Bound">m</a> <a id="13475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#13445" class="Bound">n</a>
<a id="13477" class="Symbol">...</a>                  <a id="13498" class="Symbol">|</a> <a id="13500" class="DottedPattern Symbol">.(</a><a id="13502" class="DottedPattern Bound">n</a> <a id="13504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="DottedPattern Function Operator">+</a> <a id="13506" class="DottedPattern Bound">m</a><a id="13507" class="DottedPattern Symbol">)</a> <a id="13509" class="Symbol">|</a> <a id="13511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>       <a id="13522" class="Symbol">=</a> <a id="13524" class="Bound">ev</a>
</pre>{% endraw %}In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)

In this case, we can avoid rewrite by simply applying the substitution
function defined earlier:
{% raw %}<pre class="Agda"><a id="even-comm″"></a><a id="14671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14671" class="Function">even-comm″</a> <a id="14682" class="Symbol">:</a> <a id="14684" class="Symbol">∀</a> <a id="14686" class="Symbol">(</a><a id="14687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14687" class="Bound">m</a> <a id="14689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14689" class="Bound">n</a> <a id="14691" class="Symbol">:</a> <a id="14693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8039" class="Datatype">ℕ</a><a id="14694" class="Symbol">)</a>
  <a id="14698" class="Symbol">→</a> <a id="14700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="14705" class="Symbol">(</a><a id="14706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14687" class="Bound">m</a> <a id="14708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="14710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14689" class="Bound">n</a><a id="14711" class="Symbol">)</a>
    <a id="14717" class="Comment">------------</a>
  <a id="14732" class="Symbol">→</a> <a id="14734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="14739" class="Symbol">(</a><a id="14740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14689" class="Bound">n</a> <a id="14742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8080" class="Function Operator">+</a> <a id="14744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14687" class="Bound">m</a><a id="14745" class="Symbol">)</a>
<a id="14747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14671" class="Function">even-comm″</a> <a id="14758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14758" class="Bound">m</a> <a id="14760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14760" class="Bound">n</a>  <a id="14763" class="Symbol">=</a>  <a id="14766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4779" class="Function">subst</a> <a id="14772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#10155" class="Datatype">even</a> <a id="14777" class="Symbol">(</a><a id="14778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#8664" class="Function">+-comm</a> <a id="14785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14758" class="Bound">m</a> <a id="14787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#14760" class="Bound">n</a><a id="14788" class="Symbol">)</a>
</pre>{% endraw %}Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.


## Leibniz equality

The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.

Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.

Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`:
{% raw %}<pre class="Agda"><a id="_≐_"></a><a id="15919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">_≐_</a> <a id="15923" class="Symbol">:</a> <a id="15925" class="Symbol">∀</a> <a id="15927" class="Symbol">{</a><a id="15928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15928" class="Bound">A</a> <a id="15930" class="Symbol">:</a> <a id="15932" class="PrimitiveType">Set</a><a id="15935" class="Symbol">}</a> <a id="15937" class="Symbol">(</a><a id="15938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15938" class="Bound">x</a> <a id="15940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15940" class="Bound">y</a> <a id="15942" class="Symbol">:</a> <a id="15944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15928" class="Bound">A</a><a id="15945" class="Symbol">)</a> <a id="15947" class="Symbol">→</a> <a id="15949" class="PrimitiveType">Set₁</a>
<a id="15954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">_≐_</a> <a id="15958" class="Symbol">{</a><a id="15959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15959" class="Bound">A</a><a id="15960" class="Symbol">}</a> <a id="15962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15962" class="Bound">x</a> <a id="15964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15964" class="Bound">y</a> <a id="15966" class="Symbol">=</a> <a id="15968" class="Symbol">∀</a> <a id="15970" class="Symbol">(</a><a id="15971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15971" class="Bound">P</a> <a id="15973" class="Symbol">:</a> <a id="15975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15959" class="Bound">A</a> <a id="15977" class="Symbol">→</a> <a id="15979" class="PrimitiveType">Set</a><a id="15982" class="Symbol">)</a> <a id="15984" class="Symbol">→</a> <a id="15986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15971" class="Bound">P</a> <a id="15988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15962" class="Bound">x</a> <a id="15990" class="Symbol">→</a> <a id="15992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15971" class="Bound">P</a> <a id="15994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15964" class="Bound">y</a>
</pre>{% endraw %}We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.

This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.

Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition:
{% raw %}<pre class="Agda"><a id="refl-≐"></a><a id="16818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16818" class="Function">refl-≐</a> <a id="16825" class="Symbol">:</a> <a id="16827" class="Symbol">∀</a> <a id="16829" class="Symbol">{</a><a id="16830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16830" class="Bound">A</a> <a id="16832" class="Symbol">:</a> <a id="16834" class="PrimitiveType">Set</a><a id="16837" class="Symbol">}</a> <a id="16839" class="Symbol">{</a><a id="16840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16840" class="Bound">x</a> <a id="16842" class="Symbol">:</a> <a id="16844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16830" class="Bound">A</a><a id="16845" class="Symbol">}</a>
  <a id="16849" class="Symbol">→</a> <a id="16851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16840" class="Bound">x</a> <a id="16853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">≐</a> <a id="16855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16840" class="Bound">x</a>
<a id="16857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16818" class="Function">refl-≐</a> <a id="16864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16864" class="Bound">P</a> <a id="16866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16866" class="Bound">Px</a>  <a id="16870" class="Symbol">=</a>  <a id="16873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16866" class="Bound">Px</a>

<a id="trans-≐"></a><a id="16877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16877" class="Function">trans-≐</a> <a id="16885" class="Symbol">:</a> <a id="16887" class="Symbol">∀</a> <a id="16889" class="Symbol">{</a><a id="16890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16890" class="Bound">A</a> <a id="16892" class="Symbol">:</a> <a id="16894" class="PrimitiveType">Set</a><a id="16897" class="Symbol">}</a> <a id="16899" class="Symbol">{</a><a id="16900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16900" class="Bound">x</a> <a id="16902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16902" class="Bound">y</a> <a id="16904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16904" class="Bound">z</a> <a id="16906" class="Symbol">:</a> <a id="16908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16890" class="Bound">A</a><a id="16909" class="Symbol">}</a>
  <a id="16913" class="Symbol">→</a> <a id="16915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16900" class="Bound">x</a> <a id="16917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">≐</a> <a id="16919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16902" class="Bound">y</a>
  <a id="16923" class="Symbol">→</a> <a id="16925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16902" class="Bound">y</a> <a id="16927" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">≐</a> <a id="16929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16904" class="Bound">z</a>
    <a id="16935" class="Comment">-----</a>
  <a id="16943" class="Symbol">→</a> <a id="16945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16900" class="Bound">x</a> <a id="16947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">≐</a> <a id="16949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16904" class="Bound">z</a>
<a id="16951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16877" class="Function">trans-≐</a> <a id="16959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16959" class="Bound">x≐y</a> <a id="16963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16963" class="Bound">y≐z</a> <a id="16967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16967" class="Bound">P</a> <a id="16969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16969" class="Bound">Px</a>  <a id="16973" class="Symbol">=</a>  <a id="16976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16963" class="Bound">y≐z</a> <a id="16980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16967" class="Bound">P</a> <a id="16982" class="Symbol">(</a><a id="16983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16959" class="Bound">x≐y</a> <a id="16987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16967" class="Bound">P</a> <a id="16989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16969" class="Bound">Px</a><a id="16991" class="Symbol">)</a>
</pre>{% endraw %}
Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well:
{% raw %}<pre class="Agda"><a id="sym-≐"></a><a id="17153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17153" class="Function">sym-≐</a> <a id="17159" class="Symbol">:</a> <a id="17161" class="Symbol">∀</a> <a id="17163" class="Symbol">{</a><a id="17164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17164" class="Bound">A</a> <a id="17166" class="Symbol">:</a> <a id="17168" class="PrimitiveType">Set</a><a id="17171" class="Symbol">}</a> <a id="17173" class="Symbol">{</a><a id="17174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17174" class="Bound">x</a> <a id="17176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17176" class="Bound">y</a> <a id="17178" class="Symbol">:</a> <a id="17180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17164" class="Bound">A</a><a id="17181" class="Symbol">}</a>
  <a id="17185" class="Symbol">→</a> <a id="17187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17174" class="Bound">x</a> <a id="17189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">≐</a> <a id="17191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17176" class="Bound">y</a>
    <a id="17197" class="Comment">-----</a>
  <a id="17205" class="Symbol">→</a> <a id="17207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17176" class="Bound">y</a> <a id="17209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">≐</a> <a id="17211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17174" class="Bound">x</a>
<a id="17213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17153" class="Function">sym-≐</a> <a id="17219" class="Symbol">{</a><a id="17220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17220" class="Bound">A</a><a id="17221" class="Symbol">}</a> <a id="17223" class="Symbol">{</a><a id="17224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17224" class="Bound">x</a><a id="17225" class="Symbol">}</a> <a id="17227" class="Symbol">{</a><a id="17228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17228" class="Bound">y</a><a id="17229" class="Symbol">}</a> <a id="17231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17231" class="Bound">x≐y</a> <a id="17235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17235" class="Bound">P</a>  <a id="17238" class="Symbol">=</a>  <a id="17241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17323" class="Function">Qy</a>
  <a id="17246" class="Keyword">where</a>
    <a id="17256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17256" class="Function">Q</a> <a id="17258" class="Symbol">:</a> <a id="17260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17220" class="Bound">A</a> <a id="17262" class="Symbol">→</a> <a id="17264" class="PrimitiveType">Set</a>
    <a id="17272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17256" class="Function">Q</a> <a id="17274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17274" class="Bound">z</a> <a id="17276" class="Symbol">=</a> <a id="17278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17235" class="Bound">P</a> <a id="17280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17274" class="Bound">z</a> <a id="17282" class="Symbol">→</a> <a id="17284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17235" class="Bound">P</a> <a id="17286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17224" class="Bound">x</a>
    <a id="17292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17292" class="Function">Qx</a> <a id="17295" class="Symbol">:</a> <a id="17297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17256" class="Function">Q</a> <a id="17299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17224" class="Bound">x</a>
    <a id="17305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17292" class="Function">Qx</a> <a id="17308" class="Symbol">=</a> <a id="17310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#16818" class="Function">refl-≐</a> <a id="17317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17235" class="Bound">P</a>
    <a id="17323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17323" class="Function">Qy</a> <a id="17326" class="Symbol">:</a> <a id="17328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17256" class="Function">Q</a> <a id="17330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17228" class="Bound">y</a>
    <a id="17336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17323" class="Function">Qy</a> <a id="17339" class="Symbol">=</a> <a id="17341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17231" class="Bound">x≐y</a> <a id="17345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17256" class="Function">Q</a> <a id="17347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#17292" class="Function">Qx</a>
</pre>{% endraw %}
Given `x ≐ y`, a specific `P`, we have to construct a proof that `P y`
implies `P x`.  To do so, we instantiate the equality with a predicate
`Q` such that `Q z` holds if `P z` implies `P x`.  The property `Q x`
is trivial by reflexivity, and hence `Q y` follows from `x ≐ y`.  But
`Q y` is exactly a proof of what we require, that `P y` implies `P x`.

We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`:
{% raw %}<pre class="Agda"><a id="≡-implies-≐"></a><a id="18008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18008" class="Function">≡-implies-≐</a> <a id="18020" class="Symbol">:</a> <a id="18022" class="Symbol">∀</a> <a id="18024" class="Symbol">{</a><a id="18025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18025" class="Bound">A</a> <a id="18027" class="Symbol">:</a> <a id="18029" class="PrimitiveType">Set</a><a id="18032" class="Symbol">}</a> <a id="18034" class="Symbol">{</a><a id="18035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18035" class="Bound">x</a> <a id="18037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18037" class="Bound">y</a> <a id="18039" class="Symbol">:</a> <a id="18041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18025" class="Bound">A</a><a id="18042" class="Symbol">}</a>
  <a id="18046" class="Symbol">→</a> <a id="18048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18035" class="Bound">x</a> <a id="18050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="18052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18037" class="Bound">y</a>
    <a id="18058" class="Comment">-----</a>
  <a id="18066" class="Symbol">→</a> <a id="18068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18035" class="Bound">x</a> <a id="18070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">≐</a> <a id="18072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18037" class="Bound">y</a>
<a id="18074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18008" class="Function">≡-implies-≐</a> <a id="18086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18086" class="Bound">x≡y</a> <a id="18090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18090" class="Bound">P</a>  <a id="18093" class="Symbol">=</a>  <a id="18096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#4779" class="Function">subst</a> <a id="18102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18090" class="Bound">P</a> <a id="18104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18086" class="Bound">x≡y</a>
</pre>{% endraw %}This direction follows from substitution, which we showed earlier.

In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`:
{% raw %}<pre class="Agda"><a id="≐-implies-≡"></a><a id="18307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18307" class="Function">≐-implies-≡</a> <a id="18319" class="Symbol">:</a> <a id="18321" class="Symbol">∀</a> <a id="18323" class="Symbol">{</a><a id="18324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18324" class="Bound">A</a> <a id="18326" class="Symbol">:</a> <a id="18328" class="PrimitiveType">Set</a><a id="18331" class="Symbol">}</a> <a id="18333" class="Symbol">{</a><a id="18334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18334" class="Bound">x</a> <a id="18336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18336" class="Bound">y</a> <a id="18338" class="Symbol">:</a> <a id="18340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18324" class="Bound">A</a><a id="18341" class="Symbol">}</a>
  <a id="18345" class="Symbol">→</a> <a id="18347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18334" class="Bound">x</a> <a id="18349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#15919" class="Function Operator">≐</a> <a id="18351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18336" class="Bound">y</a>
    <a id="18357" class="Comment">-----</a>
  <a id="18365" class="Symbol">→</a> <a id="18367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18334" class="Bound">x</a> <a id="18369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="18371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18336" class="Bound">y</a>
<a id="18373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18307" class="Function">≐-implies-≡</a> <a id="18385" class="Symbol">{</a><a id="18386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18386" class="Bound">A</a><a id="18387" class="Symbol">}</a> <a id="18389" class="Symbol">{</a><a id="18390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18390" class="Bound">x</a><a id="18391" class="Symbol">}</a> <a id="18393" class="Symbol">{</a><a id="18394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18394" class="Bound">y</a><a id="18395" class="Symbol">}</a> <a id="18397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18397" class="Bound">x≐y</a>  <a id="18402" class="Symbol">=</a>  <a id="18405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18479" class="Function">Qy</a>
  <a id="18410" class="Keyword">where</a>
    <a id="18420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18420" class="Function">Q</a> <a id="18422" class="Symbol">:</a> <a id="18424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18386" class="Bound">A</a> <a id="18426" class="Symbol">→</a> <a id="18428" class="PrimitiveType">Set</a>
    <a id="18436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18420" class="Function">Q</a> <a id="18438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18438" class="Bound">z</a> <a id="18440" class="Symbol">=</a> <a id="18442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18390" class="Bound">x</a> <a id="18444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#730" class="Datatype Operator">≡</a> <a id="18446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18438" class="Bound">z</a>
    <a id="18452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18452" class="Function">Qx</a> <a id="18455" class="Symbol">:</a> <a id="18457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18420" class="Function">Q</a> <a id="18459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18390" class="Bound">x</a>
    <a id="18465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18452" class="Function">Qx</a> <a id="18468" class="Symbol">=</a> <a id="18470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#770" class="InductiveConstructor">refl</a>
    <a id="18479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18479" class="Function">Qy</a> <a id="18482" class="Symbol">:</a> <a id="18484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18420" class="Function">Q</a> <a id="18486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18394" class="Bound">y</a>
    <a id="18492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18479" class="Function">Qy</a> <a id="18495" class="Symbol">=</a> <a id="18497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18397" class="Bound">x≐y</a> <a id="18501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18420" class="Function">Q</a> <a id="18503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#18452" class="Function">Qx</a>
</pre>{% endraw %}The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.

(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)


## Universe polymorphism {#unipoly}

As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?

The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following:
{% raw %}<pre class="Agda"><a id="19658" class="Keyword">open</a> <a id="19663" class="Keyword">import</a> <a id="19670" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="19676" class="Keyword">using</a> <a id="19682" class="Symbol">(</a><a id="19683" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="19688" class="Symbol">;</a> <a id="19690" href="Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="19693" class="Symbol">)</a> <a id="19695" class="Keyword">renaming</a> <a id="19704" class="Symbol">(</a><a id="19705" href="Agda.Primitive.html#611" class="Primitive">zero</a> <a id="19710" class="Symbol">to</a> <a id="19713" href="Agda.Primitive.html#611" class="Primitive">lzero</a><a id="19718" class="Symbol">;</a> <a id="19720" href="Agda.Primitive.html#627" class="Primitive">suc</a> <a id="19724" class="Symbol">to</a> <a id="19727" href="Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="19731" class="Symbol">)</a>
</pre>{% endraw %}We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.

Levels are isomorphic to natural numbers, and have similar constructors:

    lzero : Level
    lsuc  : Level → Level

The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

and so on. There is also an operator

    _⊔_ : Level → Level → Level

that given two levels returns the larger of the two.

Here is the definition of equality, generalised to an arbitrary level:
{% raw %}<pre class="Agda"><a id="20299" class="Keyword">data</a> <a id="_≡′_"></a><a id="20304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20304" class="Datatype Operator">_≡′_</a> <a id="20309" class="Symbol">{</a><a id="20310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20310" class="Bound">ℓ</a> <a id="20312" class="Symbol">:</a> <a id="20314" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="20319" class="Symbol">}</a> <a id="20321" class="Symbol">{</a><a id="20322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20322" class="Bound">A</a> <a id="20324" class="Symbol">:</a> <a id="20326" class="PrimitiveType">Set</a> <a id="20330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20310" class="Bound">ℓ</a><a id="20331" class="Symbol">}</a> <a id="20333" class="Symbol">(</a><a id="20334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20334" class="Bound">x</a> <a id="20336" class="Symbol">:</a> <a id="20338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20322" class="Bound">A</a><a id="20339" class="Symbol">)</a> <a id="20341" class="Symbol">:</a> <a id="20343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20322" class="Bound">A</a> <a id="20345" class="Symbol">→</a> <a id="20347" class="PrimitiveType">Set</a> <a id="20351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20310" class="Bound">ℓ</a> <a id="20353" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="20361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20361" class="InductiveConstructor">refl′</a> <a id="20367" class="Symbol">:</a> <a id="20369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20334" class="Bound">x</a> <a id="20371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20304" class="Datatype Operator">≡′</a> <a id="20374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20334" class="Bound">x</a>
</pre>{% endraw %}Similarly, here is the generalised definition of symmetry:
{% raw %}<pre class="Agda"><a id="sym′"></a><a id="20443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20443" class="Function">sym′</a> <a id="20448" class="Symbol">:</a> <a id="20450" class="Symbol">∀</a> <a id="20452" class="Symbol">{</a><a id="20453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20453" class="Bound">ℓ</a> <a id="20455" class="Symbol">:</a> <a id="20457" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="20462" class="Symbol">}</a> <a id="20464" class="Symbol">{</a><a id="20465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20465" class="Bound">A</a> <a id="20467" class="Symbol">:</a> <a id="20469" class="PrimitiveType">Set</a> <a id="20473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20453" class="Bound">ℓ</a><a id="20474" class="Symbol">}</a> <a id="20476" class="Symbol">{</a><a id="20477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20477" class="Bound">x</a> <a id="20479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20479" class="Bound">y</a> <a id="20481" class="Symbol">:</a> <a id="20483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20465" class="Bound">A</a><a id="20484" class="Symbol">}</a>
  <a id="20488" class="Symbol">→</a> <a id="20490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20477" class="Bound">x</a> <a id="20492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20304" class="Datatype Operator">≡′</a> <a id="20495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20479" class="Bound">y</a>
    <a id="20501" class="Comment">------</a>
  <a id="20510" class="Symbol">→</a> <a id="20512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20479" class="Bound">y</a> <a id="20514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20304" class="Datatype Operator">≡′</a> <a id="20517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20477" class="Bound">x</a>
<a id="20519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20443" class="Function">sym′</a> <a id="20524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20361" class="InductiveConstructor">refl′</a> <a id="20530" class="Symbol">=</a> <a id="20532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20361" class="InductiveConstructor">refl′</a>
</pre>{% endraw %}For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.

Here is the generalised definition of Leibniz equality:
{% raw %}<pre class="Agda"><a id="_≐′_"></a><a id="20810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20810" class="Function Operator">_≐′_</a> <a id="20815" class="Symbol">:</a> <a id="20817" class="Symbol">∀</a> <a id="20819" class="Symbol">{</a><a id="20820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20820" class="Bound">ℓ</a> <a id="20822" class="Symbol">:</a> <a id="20824" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="20829" class="Symbol">}</a> <a id="20831" class="Symbol">{</a><a id="20832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20832" class="Bound">A</a> <a id="20834" class="Symbol">:</a> <a id="20836" class="PrimitiveType">Set</a> <a id="20840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20820" class="Bound">ℓ</a><a id="20841" class="Symbol">}</a> <a id="20843" class="Symbol">(</a><a id="20844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20844" class="Bound">x</a> <a id="20846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20846" class="Bound">y</a> <a id="20848" class="Symbol">:</a> <a id="20850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20832" class="Bound">A</a><a id="20851" class="Symbol">)</a> <a id="20853" class="Symbol">→</a> <a id="20855" class="PrimitiveType">Set</a> <a id="20859" class="Symbol">(</a><a id="20860" href="Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="20865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20820" class="Bound">ℓ</a><a id="20866" class="Symbol">)</a>
<a id="20868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20810" class="Function Operator">_≐′_</a> <a id="20873" class="Symbol">{</a><a id="20874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20874" class="Bound">ℓ</a><a id="20875" class="Symbol">}</a> <a id="20877" class="Symbol">{</a><a id="20878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20878" class="Bound">A</a><a id="20879" class="Symbol">}</a> <a id="20881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20881" class="Bound">x</a> <a id="20883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20883" class="Bound">y</a> <a id="20885" class="Symbol">=</a> <a id="20887" class="Symbol">∀</a> <a id="20889" class="Symbol">(</a><a id="20890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20890" class="Bound">P</a> <a id="20892" class="Symbol">:</a> <a id="20894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20878" class="Bound">A</a> <a id="20896" class="Symbol">→</a> <a id="20898" class="PrimitiveType">Set</a> <a id="20902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20874" class="Bound">ℓ</a><a id="20903" class="Symbol">)</a> <a id="20905" class="Symbol">→</a> <a id="20907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20890" class="Bound">P</a> <a id="20909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20881" class="Bound">x</a> <a id="20911" class="Symbol">→</a> <a id="20913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20890" class="Bound">P</a> <a id="20915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#20883" class="Bound">y</a>
</pre>{% endraw %}Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.

Most other functions in the standard library are also generalised to
arbitrary levels. For instance, here is the definition of composition.
{% raw %}<pre class="Agda"><a id="_∘_"></a><a id="21234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21234" class="Function Operator">_∘_</a> <a id="21238" class="Symbol">:</a> <a id="21240" class="Symbol">∀</a> <a id="21242" class="Symbol">{</a><a id="21243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21243" class="Bound">ℓ₁</a> <a id="21246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21246" class="Bound">ℓ₂</a> <a id="21249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21249" class="Bound">ℓ₃</a> <a id="21252" class="Symbol">:</a> <a id="21254" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="21259" class="Symbol">}</a> <a id="21261" class="Symbol">{</a><a id="21262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21262" class="Bound">A</a> <a id="21264" class="Symbol">:</a> <a id="21266" class="PrimitiveType">Set</a> <a id="21270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21243" class="Bound">ℓ₁</a><a id="21272" class="Symbol">}</a> <a id="21274" class="Symbol">{</a><a id="21275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21275" class="Bound">B</a> <a id="21277" class="Symbol">:</a> <a id="21279" class="PrimitiveType">Set</a> <a id="21283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21246" class="Bound">ℓ₂</a><a id="21285" class="Symbol">}</a> <a id="21287" class="Symbol">{</a><a id="21288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21288" class="Bound">C</a> <a id="21290" class="Symbol">:</a> <a id="21292" class="PrimitiveType">Set</a> <a id="21296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21249" class="Bound">ℓ₃</a><a id="21298" class="Symbol">}</a>
  <a id="21302" class="Symbol">→</a> <a id="21304" class="Symbol">(</a><a id="21305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21275" class="Bound">B</a> <a id="21307" class="Symbol">→</a> <a id="21309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21288" class="Bound">C</a><a id="21310" class="Symbol">)</a> <a id="21312" class="Symbol">→</a> <a id="21314" class="Symbol">(</a><a id="21315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21262" class="Bound">A</a> <a id="21317" class="Symbol">→</a> <a id="21319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21275" class="Bound">B</a><a id="21320" class="Symbol">)</a> <a id="21322" class="Symbol">→</a> <a id="21324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21262" class="Bound">A</a> <a id="21326" class="Symbol">→</a> <a id="21328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21288" class="Bound">C</a>
<a id="21330" class="Symbol">(</a><a id="21331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21331" class="Bound">g</a> <a id="21333" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21234" class="Function Operator">∘</a> <a id="21335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21335" class="Bound">f</a><a id="21336" class="Symbol">)</a> <a id="21338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21338" class="Bound">x</a>  <a id="21341" class="Symbol">=</a>  <a id="21344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21331" class="Bound">g</a> <a id="21346" class="Symbol">(</a><a id="21347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21335" class="Bound">f</a> <a id="21349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Equality.md %}{% raw %}#21338" class="Bound">x</a><a id="21350" class="Symbol">)</a>
</pre>{% endraw %}
Further information on levels can be found in the [Agda Wiki][wiki].

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


## Standard library

Definitions similar to those in this chapter can be found in the
standard library:
{% raw %}<pre class="Agda"><a id="21631" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="21685" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="21749" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>
</pre>{% endraw %}Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.


## Unicode

This chapter uses the following unicode:

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
