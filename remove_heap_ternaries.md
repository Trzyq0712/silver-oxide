# Removing heap ternaries

```viper
if (b) {
    inhale acc(x.f, 1/2) && x.f == 0
} else {
    inhale acc(x.f, 1/1) && x.f == 1
}
```

## With ternaries
```vmir
h0 := <b> acc(f(x), 1/2) // -> v0
h1 := <b> h_in + h0
e0 := <b> *[h1] f(x)
assume <b> e_0 == 0

h2 := <!b> acc(f(x), 1/1) // -> v1
h3 := <!b> h_in + h2
e1 := <!b> *[h3] f(x)
assume <!b> e_1 == 1

h_out := b ? h1 : h3
```

## Without ternaries (initial)
```vmir
h0 := <b> acc(f(x), b ? 1/2 : none) // -> b ? v0 : v0'
h1 := <b> h_in + h0
e0 := <b> *[h1] f(x) // p = 1/2 > none
assume <b> e0 == 0  // v = v0

h2 := <!b> acc(f(x), b ? none : 1/1) // -> b ? v1' : v1
h3 := <!b> h1 + h2
e1 := <!b> *[h3] f(x) // p = 1/1 > none
assume <!b> e1 == 1 // v = v1

h_out := h3
```

## Without ternaries (final)
```vmir
h0 := <b> acc(f(x), b ? 1/2 : none) // -> v0
h1 := <b> h_in + h0
e0 := <b> *[h1] f(x) // p = 1/2 > none
assume <b> e0 == 0  // v = v0

h2 := <!b> acc(f(x), b ? none : 1/1) // -> v1
h3 := <!b> h1 + h2
e1 := <!b> *[h3] f(x) // p = 1/1 > none
assume <!b> e1 == 1 // v = v1

h_out := h3
```

It is sufficient to have plain `v0` and `v1` stored at `h0` and `h2` respectively.
This is because when we execute `h3 := <!b> h1 + h2`, the following happens:

- New permission amount is `p' := p0 + p1` with `p0 = b ? 1/2 : none` and
  `p1 = b ? none : 1/1`, effectively giving us `p' := b ? 1/2 : none + b ? none : 1/1`
- New value is `v' := p0 > none ? v0 : v1`
- We emit an agreement axiom `p0 > none && p1 > none ==> v0 == v1`. These, 
  however, cannot be both true at the same time, effectively meaning that `v0` 
  and `v1` are never equated.

Actually, this means we can even remove the path condition from heap additions, as the path condition is actually already embedded in the permission amounts.

We still need the path conditions for `acc` to check that the permission amount is `> none`.

### Actual final version
```vmir
h0 := <b> acc(f(x), b ? 1/2 : none) // -> v0
h1 := h_in + h0
e0 := <b> *[h1] f(x)   // p = 1/2 > none
assume <b> e0 == 0     // v = v0

h2 := <!b> acc(f(x), b ? none : 1/1) // -> v1
h3 := h1 + h2
e1 := <!b> *[h3] f(x)  // p = 1/1 > none
assume <!b> e2 == 1    // v = v1

h_out := h3
```

If we fully commit to this approach, we would be probably completely linearizing methods' control flow graphs, which we were not a 100% sure we wanted to do. This is relevant from the point of path prunning, which afaik Silicon does, i.e. it does not explore blocks which are unreachable. But honestly, I don't know how large of a benefit that is in practice, especially in Prusti-generated Viper code.

## A case against removing heap ternaries
In theory, we could execute both branches in parallel and then merge the resulting heaps at the end, something like a work stealing scheduler. I'm guessing that might not even give significant improvements in practice, food for thought though.
