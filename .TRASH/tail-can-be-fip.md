# HOW TO from type signature only in granule - see that


## | **`fip`**     | ❌ **0** destroyed   | ❌ **0** created |

-- fip: 0 created, 0 destroyed
-- Takes a unique list, transforms its pointers, returns a unique list of the same structure.
reverse : *List a -> *List a

## | **`fip(1)`**  | ❌ **0** destroyed   | ✅ **1** created |

-- fip(1): 0 destroyed, 1 created
-- Takes a linear element `a` and appends it to an existing `*List a`, creating 1 new node.
cons : a -> *List a -> *List a

-- Or creating a single unique node from scratch:
single : a -> *List a

## | **`fbip`**    | ✅ **Any** destroyed | ❌ **0** created |

## | **`fbip(1)`** | ✅ **Any** destroyed | ✅ **1** created |


TODO???

```granule
-- A function that consumes a unique list and performs 0 heap allocations:
reverse : *List a -> *List a <Alloc 0>

-- A function that consumes a unique list and performs exactly 1 heap allocation:
cons : a -> *List a -> *List a <Alloc 1>

-- A function that drops/frees a node:
tail : *List a -> *List a <Free 1>
```

```
uncons : *List a -> (a, *List a)
uncons (Cons x xs) = (x, xs)
uncons Nil         = ... -- handle empty list
```
