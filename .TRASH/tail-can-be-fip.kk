// | Annotation    | Can destroy/drop?    | Can create without recycling? (Fresh allocations) |
// | :---          | :---                 | :---             |
// | **`fip`**     | ❌ **0** destroyed   | ❌ **0** created |
// | **`fip(1)`**  | ❌ **0** destroyed   | ✅ **1** created |
// | **`fbip`**    | ✅ **Any** destroyed | ❌ **0** created |
// | **`fbip(1)`** | ✅ **Any** destroyed | ✅ **1** created |

// warning: fip(1) fun tail: binding a wildcard pattern of type 35 causes deallocation
// warning: fip(1) fun tail: the matched constructor Cons/16 is not reused
fip(1) fun tail( xs : list<a> ) : list<a>
  match xs
    Cons(_, xx) -> xx
    _           -> []

// warning: fbip fun create_node: function allocates at most 1 but was declared as allocating nothing
fbip fun create_node() : list<int>
  [1]

fun main()
  println("foo")
