library Y {
    event E() anonymous;
}

contract C {
    function test1() external pure returns (bytes32) {
        return Y.E.selector;
    }

    bytes32 s5 = Y.E.selector;

    function test2() view external returns (bytes32) {
        return s5;
    }
}
// ----
// TypeError 9582: (123-135): Member "selector" not found or not visible after argument-dependent lookup in function ().
