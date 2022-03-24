abstract contract A {
	function foo() public virtual view returns(uint[] calldata);
}
contract X is A {
	function foo() public view override returns(uint[] memory) {  }
}
// ----
// TypeError 1443: (105-168): Data locations of return variables have to be the same when overriding, but they differ.
