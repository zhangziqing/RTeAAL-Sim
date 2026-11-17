circuit NestedAccess :
  module NestedAccess :
    input clock : Clock
    input reset : UInt<1>
    input row : UInt<3>
    input column : UInt<3>
    input value : UInt<8>
    output out : UInt<8>
    reg slots : { foo : UInt<8>[3], bar : { a : UInt<4>, b : UInt<8> }[2] }[4], clock
    slots[0].foo[0] <= mux(reset, UInt<8>(0), slots[0].foo[0])
    slots[0].foo[1] <= mux(reset, UInt<8>(0), slots[0].foo[1])
    slots[0].foo[2] <= mux(reset, UInt<8>(0), slots[0].foo[2])
    slots[0].bar[0].a <= mux(reset, UInt<4>(0), slots[0].bar[0].a)
    slots[0].bar[0].b <= mux(reset, UInt<8>(0), slots[0].bar[0].b)
    slots[0].bar[1].a <= mux(reset, UInt<4>(0), slots[0].bar[1].a)
    slots[0].bar[1].b <= mux(reset, UInt<8>(0), slots[0].bar[1].b)
    slots[1].foo[0] <= mux(reset, UInt<8>(0), slots[1].foo[0])
    slots[1].foo[1] <= mux(reset, UInt<8>(0), slots[1].foo[1])
    slots[1].foo[2] <= mux(reset, UInt<8>(0), slots[1].foo[2])
    slots[1].bar[0].a <= mux(reset, UInt<4>(0), slots[1].bar[0].a)
    slots[1].bar[0].b <= mux(reset, UInt<8>(0), slots[1].bar[0].b)
    slots[1].bar[1].a <= mux(reset, UInt<4>(0), slots[1].bar[1].a)
    slots[1].bar[1].b <= mux(reset, UInt<8>(0), slots[1].bar[1].b)
    slots[2].foo[0] <= mux(reset, UInt<8>(0), slots[2].foo[0])
    slots[2].foo[1] <= mux(reset, UInt<8>(0), slots[2].foo[1])
    slots[2].foo[2] <= mux(reset, UInt<8>(0), slots[2].foo[2])
    slots[2].bar[0].a <= mux(reset, UInt<4>(0), slots[2].bar[0].a)
    slots[2].bar[0].b <= mux(reset, UInt<8>(0), slots[2].bar[0].b)
    slots[2].bar[1].a <= mux(reset, UInt<4>(0), slots[2].bar[1].a)
    slots[2].bar[1].b <= mux(reset, UInt<8>(0), slots[2].bar[1].b)
    slots[3].foo[0] <= mux(reset, UInt<8>(0), slots[3].foo[0])
    slots[3].foo[1] <= mux(reset, UInt<8>(0), slots[3].foo[1])
    slots[3].foo[2] <= mux(reset, UInt<8>(0), slots[3].foo[2])
    slots[3].bar[0].a <= mux(reset, UInt<4>(0), slots[3].bar[0].a)
    slots[3].bar[0].b <= mux(reset, UInt<8>(0), slots[3].bar[0].b)
    slots[3].bar[1].a <= mux(reset, UInt<4>(0), slots[3].bar[1].a)
    slots[3].bar[1].b <= mux(reset, UInt<8>(0), slots[3].bar[1].b)
    when not(reset) :
      slots[row].foo[column] <= value
      slots[column].bar[row].a <= bits(value, 3, 0)
      slots[row].bar[column].b <= value
    out <= xor(slots[column].foo[row], slots[row].bar[column].b)
