contract C {
    uint8[3] st = [1, 2, 3];
    uint[] dt = [4, 5, 6]; // TODO: when uint8[] in use, compiler raise an error: Could not convert "uint8[]" to internal ABI type representation. Falling back to default encoding.

    function s() public returns (uint8[3] memory) {
        return st;
    }

    function d() public returns (uint[] memory) {
        return dt;
    }
}

// ====
// compileToEwasm: also
// compileViaYul: also
// ----
// s() -> 1, 2, 3
// d() -> 0x20, 3, 4, 5, 6
