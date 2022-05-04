/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsmtutil/CHCSmtLib2Interface.h>

#include <libsolutil/Algorithms.h>
#include <libsolutil/Keccak256.h>

#include <boost/algorithm/string/join.hpp>
#include <boost/algorithm/string/predicate.hpp>

#include <range/v3/view.hpp>
#include <range/v3/algorithm/for_each.hpp>

#include <array>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>

using namespace std;
using namespace solidity;
using namespace solidity::util;
using namespace solidity::frontend;
using namespace solidity::smtutil;

CHCSmtLib2Interface::CHCSmtLib2Interface(
	map<h256, string> const& _queryResponses,
	ReadCallback::Callback _smtCallback,
	optional<unsigned> _queryTimeout
):
	CHCSolverInterface(_queryTimeout),
	m_smtlib2(make_unique<SMTLib2Interface>(_queryResponses, _smtCallback, m_queryTimeout)),
	m_queryResponses(move(_queryResponses)),
	m_smtCallback(_smtCallback)
{
	reset();
}

void CHCSmtLib2Interface::reset()
{
	m_accumulatedOutput.clear();
	m_variables.clear();
	m_unhandledQueries.clear();
	m_sortNames.clear();
}

void CHCSmtLib2Interface::registerRelation(Expression const& _expr)
{
	smtAssert(_expr.sort);
	smtAssert(_expr.sort->kind == Kind::Function);
	if (!m_variables.count(_expr.name))
	{
		auto fSort = dynamic_pointer_cast<FunctionSort>(_expr.sort);
		string domain = toSmtLibSort(fSort->domain);
		// Relations are predicates which have implicit codomain Bool.
		m_variables.insert(_expr.name);
		write(
			"(declare-fun |" +
			_expr.name +
			"| " +
			domain +
			" Bool)"
		);
	}
}

void CHCSmtLib2Interface::addRule(Expression const& _expr, std::string const& /*_name*/)
{
	write(
		"(assert\n(forall " + forall() + "\n" +
		m_smtlib2->toSExpr(_expr) +
		"))\n\n"
	);
}

tuple<CheckResult, Expression, CHCSolverInterface::CexGraph> CHCSmtLib2Interface::query(Expression const& _block)
{
	string accumulated{};
	swap(m_accumulatedOutput, accumulated);
	solAssert(m_smtlib2, "");
	writeHeader();
	for (auto const& decl: m_smtlib2->userSorts() | ranges::views::values)
		write(decl);
	m_accumulatedOutput += accumulated;

	string queryRule = "(assert\n(forall " + forall() + "\n" +
		"(=> " + _block.name + " false)"
		"))";
	string response = querySolver(
		m_accumulatedOutput +
		queryRule +
		"\n(check-sat)"
	);
	swap(m_accumulatedOutput, accumulated);

	CheckResult result;
	// TODO proper parsing
	if (boost::starts_with(response, "sat"))
		return {CheckResult::UNSATISFIABLE, parseInvariants(response), {}};
	else if (boost::starts_with(response, "unsat"))
		return {CheckResult::SATISFIABLE, Expression (true), parseCounterexample(response)};
	else if (boost::starts_with(response, "unknown"))
		result = CheckResult::UNKNOWN;
	else
		result = CheckResult::ERROR;

	return {result, Expression(true), {}};
}

namespace
{

string readToken(string const& _data, size_t _pos)
{
	string r;
	while (_pos < _data.size())
	{
		char c = _data[_pos++];
		if (iswspace(unsigned(c)) || c == ',' || c == '(' || c == ')')
			break;
		r += c;
	}
	return r;
}

size_t skipWhitespaces(string const& _data, size_t _pos)
{
	while (_pos < _data.size() && iswspace(unsigned(_data[_pos])))
	{
		++_pos;
	}

	return _pos;
}

/// @param _data here is always going to be either
/// - term
/// - term(args)
pair<smtutil::Expression, size_t> parseExpression(string const& _data)
{
	size_t pos = skipWhitespaces(_data, 0);

	string fname = readToken(_data, pos);
	pos += fname.size();

	if (pos >= _data.size() || _data[pos] != '(')
	{
		if (fname == "true" || fname == "false")
			return {Expression(fname, {}, SortProvider::boolSort), pos};
		return {Expression(fname, {}, SortProvider::uintSort), pos};
	}

	smtAssert(_data[pos] == '(');

	vector<Expression> exprArgs;
	do
	{
		++pos;
		auto [arg, size] = parseExpression(_data.substr(pos));
		pos += size;
		exprArgs.emplace_back(move(arg));
		smtAssert(_data[pos] == ',' || _data[pos] == ')');
	} while (_data[pos] == ',');

	smtAssert(_data[pos] == ')');
	++pos;

	if (fname == "const")
		fname = "const_array";

	return {Expression(fname, move(exprArgs), SortProvider::uintSort), pos};
}

/// @param _data here is always going to be either
/// - term
/// - (term arg1 arg2 ... argk), where each arg is an sexpr.
pair<smtutil::Expression, size_t> parseSExpression(string const& _data)
{
	size_t pos = skipWhitespaces(_data, 0);

	vector<Expression> exprArgs;
	string fname;
	if (_data[pos] != '(')
	{
		fname = readToken(_data, pos);
		pos += fname.size();
	}
	else
	{
		++pos;

		/*
		fname = readToken(_data, pos);
		pos += fname.size();
		do
		{
			auto [symbArg, newPos] = parseSExpression(_data.substr(pos));
			exprArgs.emplace_back(move(symbArg));
			pos += newPos;
		} while (_data[pos] != ')');
		++pos;
		*/

		string subExpr = _data.substr(pos);
		string target = "(as const ";
		if (boost::starts_with(subExpr, target))
		{
			fname = "const_array";
			pos += target.size();
			auto [symbArg, newPos] = parseSExpression(_data.substr(pos));
			exprArgs.emplace_back(move(symbArg));
			pos += newPos;
			++pos;
		}
		else
		{
			fname = readToken(_data, pos);
			pos += fname.size();
		}

		do
		{
			auto [symbArg, newPos] = parseSExpression(_data.substr(pos));
			//cout << symbArg.name
			exprArgs.emplace_back(move(symbArg));
			pos += newPos;
		} while (_data[pos] != ')');
		++pos;
	}

	if (fname == "")
		fname = "var-decl";
	else if (fname == "const")
		fname = "const_array";

	if (fname == "true" || fname == "false")
		return {Expression(fname, {}, SortProvider::boolSort), pos};

	return {Expression(fname, move(exprArgs), SortProvider::uintSort), pos};
}

smtutil::Expression parseDefineFun(string const& _data)
{
	auto [defineFun, pos] = parseSExpression(_data);

	vector<Expression> newArgs;
	Expression const& curArgs = defineFun.arguments.at(1);
	smtAssert(curArgs.name == "var-decl");
	for (auto&& curArg: curArgs.arguments)
		newArgs.emplace_back(move(curArg));

	Expression predExpr{defineFun.arguments.at(0).name, move(newArgs), SortProvider::boolSort};

	Expression& invExpr = defineFun.arguments.at(3);

	solidity::util::BreadthFirstSearch<Expression*> bfs{{&invExpr}};
	bfs.run([&](auto&& _expr, auto&& _addChild) {
		if (_expr->name == "=")
		{
			smtAssert(_expr->arguments.size() == 2);
			auto check = [](string const& _name) {
				return boost::starts_with(_name, "mapping") && boost::ends_with(_name, "length");
			};
			if (check(_expr->arguments.at(0).name) || check(_expr->arguments.at(1).name))
				*_expr = Expression(true);
		}
		for (auto& arg: _expr->arguments)
			_addChild(&arg);
	});

	Expression eq{"=", {move(predExpr), move(defineFun.arguments.at(3))}, SortProvider::boolSort};

	return eq;
}

}

CHCSolverInterface::CexGraph CHCSmtLib2Interface::parseCounterexample(string const& _result)
{
	CHCSolverInterface::CexGraph cexGraph;

	for (auto&& line: _result | ranges::views::split('\n') | ranges::to<vector<string>>())
	{
		string firstDelimiter = ": ";
		string secondDelimiter = " -> ";

		size_t f = line.find(firstDelimiter);
		if (f != string::npos)
		{
			string id = line.substr(0, f);
			string rest = line.substr(f + firstDelimiter.size());

			size_t s = rest.find(secondDelimiter);
			string pred;
			string adj;
			if (s == string::npos)
				pred = rest;
			else
			{
				pred = rest.substr(0, s);
				adj = rest.substr(s + secondDelimiter.size());
			}

			if (pred == "FALSE")
				pred = "false";

			unsigned iid = unsigned(stoi(id));

			vector<unsigned> children;
			for (auto&& v: adj | ranges::views::split(',') | ranges::to<vector<string>>())
				children.emplace_back(unsigned(stoi(v)));

			auto [expr, size] = parseExpression(pred);

			cexGraph.nodes.emplace(iid, move(expr));
			cexGraph.edges.emplace(iid, move(children));
		}
	}

	return cexGraph;
}

Expression CHCSmtLib2Interface::parseInvariants(string const& _result)
{
	vector<Expression> eqs;
	for (auto&& line: _result | ranges::views::split('\n') | ranges::to<vector<string>>())
	{
		if (!boost::starts_with(line, "(define-fun"))
			continue;

		eqs.emplace_back(parseDefineFun(line));
	}

	Expression conj{"and", move(eqs), SortProvider::boolSort};
	return conj;
}

void CHCSmtLib2Interface::declareVariable(string const& _name, SortPointer const& _sort)
{
	smtAssert(_sort);
	if (_sort->kind == Kind::Function)
		declareFunction(_name, _sort);
	else if (!m_variables.count(_name))
	{
		m_variables.insert(_name);
		write("(declare-var |" + _name + "| " + toSmtLibSort(*_sort) + ')');
	}
}

string CHCSmtLib2Interface::toSmtLibSort(Sort const& _sort)
{
	if (!m_sortNames.count(&_sort))
		m_sortNames[&_sort] = m_smtlib2->toSmtLibSort(_sort);
	return m_sortNames.at(&_sort);
}

string CHCSmtLib2Interface::toSmtLibSort(vector<SortPointer> const& _sorts)
{
	string ssort("(");
	for (auto const& sort: _sorts)
		ssort += toSmtLibSort(*sort) + " ";
	ssort += ")";
	return ssort;
}

void CHCSmtLib2Interface::writeHeader()
{
	if (m_queryTimeout)
		write("(set-option :timeout " + to_string(*m_queryTimeout) + ")");
	write("(set-logic HORN)\n");
}

string CHCSmtLib2Interface::forall()
{
	string vars("(");
	for (auto const& [name, sort]: m_smtlib2->variables())
	{
		solAssert(sort, "");
		if (sort->kind != Kind::Function)
			vars += " (" + name + " " + toSmtLibSort(*sort) + ")";
	}
	vars += ")";
	return vars;
}

void CHCSmtLib2Interface::declareFunction(string const& _name, SortPointer const& _sort)
{
	smtAssert(_sort);
	smtAssert(_sort->kind == Kind::Function);
	// TODO Use domain and codomain as key as well
	if (!m_variables.count(_name))
	{
		auto fSort = dynamic_pointer_cast<FunctionSort>(_sort);
		smtAssert(fSort->codomain);
		string domain = toSmtLibSort(fSort->domain);
		string codomain = toSmtLibSort(*fSort->codomain);
		m_variables.insert(_name);
		write(
			"(declare-fun |" +
			_name +
			"| " +
			domain +
			" " +
			codomain +
			")"
		);
	}
}

void CHCSmtLib2Interface::write(string _data)
{
	m_accumulatedOutput += move(_data) + "\n";
}

string CHCSmtLib2Interface::querySolver(string const& _input)
{
	/*
	return "unsat\n\
\n\
0: FALSE -> 1\n\
1: error_target_14_0 -> 8, 2\n\
2: summary_4_function_abiDecodeArray__250_251_0(1, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(store(store(store(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639957), 0, 205), 1, 52), 2, 94), 3, 185), 4), 1461501637330902918203684832716283019655932542975, 3442761401, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0)) -> 4, 3\n\
3: block_20_function_abiDecodeArray__250_251_0(0, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(store(store(store(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639957), 0, 205), 1, 52), 2, 94), 3, 185), 4), 1461501637330902918203684832716283019655932542975, 3442761401, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), uint_array_tuple(const(0), 1), uint_array_tuple(const(0), 1), uint_array_tuple(const(0), 1), uint_array_tuple(const(0), 1), uint_array_tuple(const(0), 1), uint_array_tuple(const(0), 1), uint_array_tuple(const(0), 1), uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 1), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 1), 0, uint_array_tuple(const(0), 1), uint_array_tuple(const(0), 1))\n\
4: summary_3_function_abiDecodeArray__250_251_0(1, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(store(store(store(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639957), 0, 205), 1, 52), 2, 94), 3, 185), 4), 1461501637330902918203684832716283019655932542975, 3442761401, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0)) -> 5\n\
5: block_8_function_abiDecodeArray__250_251_0(1, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(store(store(store(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639957), 0, 205), 1, 52), 2, 94), 3, 185), 4), 1461501637330902918203684832716283019655932542975, 3442761401, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0, uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)) -> 6\n\
6: block_6_abiDecodeArray_249_251_0(0, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(store(store(store(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639957), 0, 205), 1, 52), 2, 94), 3, 185), 4), 1461501637330902918203684832716283019655932542975, 3442761401, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0, uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)) -> 7\n\
7: block_5_function_abiDecodeArray__250_251_0(0, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(store(store(store(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639957), 0, 205), 1, 52), 2, 94), 3, 185), 4), 1461501637330902918203684832716283019655932542975, 3442761401, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), bytes_tuple(store(const(0), 1, 1), 0), bytes_tuple(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0, uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))\n\
8: interface_0_C_251_0(115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935))) -> 9\n\
9: summary_constructor_2_C_251_0(0, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(const(0), 0), 1461501637330902918203684832716283019655932542975, 0, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935))) -> 10, 13\n\
10: contract_initializer_21_C_251_0(0, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(const(0), 0), 1461501637330902918203684832716283019655932542975, 0, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935))) -> 11\n\
11: contract_initializer_after_init_23_C_251_0(0, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(const(0), 0), 1461501637330902918203684832716283019655932542975, 0, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935))) -> 12\n\
12: contract_initializer_entry_22_C_251_0(0, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(const(0), 0), 1461501637330902918203684832716283019655932542975, 0, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)))\n\
13: implicit_constructor_entry_24_C_251_0(0, 115792089237316195423570985008687907853269984665640564039457584007913129639944, abi_type(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr_t_array(t_array(t_array(t_uint256)dyn_memory_ptr)dyn_memory_ptr)dyn_memory_ptr_t_uint256_input(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0), uint_array_tuple_array_tuple_array_tuple(const(uint_array_tuple_array_tuple(const(uint_array_tuple(const(0), 0)), 0)), 0), 0)), store(const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0))), bytes_tuple(store(const(0), 1, 1), 0), t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(store(const(0), 0, 1), 115792089237316195423570985008687907853269984665640564039457584007913129639935), uint_array_tuple(const(0), 0))), const(t_function_abidecode_pure()returns()_t_bytes_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_t_array(t_uint256)dyn_memory_ptr_input(uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0), uint_array_tuple(const(0), 0)))), crypto_type(const(0), const(0), const(0), const(0)), tx_type(115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, store(const(115792089237316195423570985008687907853269984665640564039457584007913129639970), 115792089237316195423570985008687907853269984665640564039457584007913129639960, 0), bytes_tuple(const(0), 0), 1461501637330902918203684832716283019655932542975, 0, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639935, 1461501637330902918203684832716283019655932542975), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)), state_type(store(const(115792089237316195423570985008687907853269984665640564039457584007913129639946), 115792089237316195423570985008687907853269984665640564039457584007913129639944, 115792089237316195423570985008687907853269984665640564039457584007913129639935)))";

*/
	/*
	return "sat\n\
(define-fun block_5_function_abiDecodeArray__57_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G bytes_tuple) (H bytes_tuple) (I state_type) (J bytes_tuple) (K bytes_tuple) (L uint_array_tuple) (M uint_array_tuple) (N uint_array_tuple) (O uint_array_tuple)) Bool true)\n\
(define-fun block_6_abiDecodeArray_56_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G bytes_tuple) (H bytes_tuple) (I state_type) (J bytes_tuple) (K bytes_tuple) (L uint_array_tuple) (M uint_array_tuple) (N uint_array_tuple) (O uint_array_tuple)) Bool (and (and (and (= K H) (= J G)) (= I F)) (= A 0)))\n\
(define-fun block_7_return_function_abiDecodeArray__57_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G bytes_tuple) (H bytes_tuple) (I state_type) (J bytes_tuple) (K bytes_tuple) (L uint_array_tuple) (M uint_array_tuple) (N uint_array_tuple) (O uint_array_tuple)) Bool (exists ((var0 |tuple(uint256[],uint256[])|)) (and (and (and (and (and (and (and (and (exists ((var1 |tuple(uint256[],uint256[])|)) (and (and (= (|tuple(uint256[],uint256[])_accessor_0| var1) (|tuple(uint256[],uint256[])_accessor_0| var0)) (= (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr_input_0 (select (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr C) G)) (|tuple(uint256[],uint256[])_accessor_0| var0))) (= (|tuple(uint256[],uint256[])_accessor_1| var1) (|tuple(uint256[],uint256[])_accessor_1| var0)))) (= (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr_input_1 (select (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr C) G)) (|tuple(uint256[],uint256[])_accessor_1| var0))) (>= (bytes_tuple_accessor_length G) 0)) (>= (bytes_tuple_accessor_length H) 0)) (<= (uint_array_tuple_accessor_length (|tuple(uint256[],uint256[])_accessor_0| var0)) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (uint_array_tuple_accessor_length (|tuple(uint256[],uint256[])_accessor_0| var0)) 0)) (= L (|tuple(uint256[],uint256[])_accessor_0| var0))) (= M (|tuple(uint256[],uint256[])_accessor_1| var0))) (and (and (and (and (and (= 0 A) (= F I)) (= G J)) (= H K)) (= (|tuple(uint256[],uint256[])_accessor_0| var0) N)) (= (|tuple(uint256[],uint256[])_accessor_1| var0) O)))))\n\
(define-fun block_8_function_abiDecodeArray__57_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G bytes_tuple) (H bytes_tuple) (I state_type) (J bytes_tuple) (K bytes_tuple) (L uint_array_tuple) (M uint_array_tuple) (N uint_array_tuple) (O uint_array_tuple)) Bool false)\n\
(define-fun block_9_function_abiDecodeArray__57_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G bytes_tuple) (H bytes_tuple) (I state_type) (J bytes_tuple) (K bytes_tuple) (L uint_array_tuple) (M uint_array_tuple) (N uint_array_tuple) (O uint_array_tuple)) Bool true)\n\
(define-fun contract_initializer_10_C_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G state_type)) Bool (and (= G F) (= A 0)))\n\
(define-fun contract_initializer_after_init_12_C_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G state_type)) Bool (and (= G F) (= A 0)))\n\
(define-fun contract_initializer_entry_11_C_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G state_type)) Bool (and (= G F) (= A 0)))\n\
(define-fun error_target_3_0 () Bool false)\n\
(define-fun implicit_constructor_entry_13_C_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G state_type)) Bool (and (>= (select (balances G) B) (msg.value E)) (and (= 0 A) (= G F))))\n\
(define-fun interface_0_C_58_0 ((A Int) (B abi_type) (C crypto_type) (D state_type)) Bool true)\n\
(define-fun nondet_interface_1_C_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E state_type) (F state_type)) Bool true)\n\
(define-fun summary_3_function_abiDecodeArray__57_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G bytes_tuple) (H bytes_tuple) (I state_type) (J bytes_tuple) (K bytes_tuple)) Bool (and (and (and (= I F) (= J G)) (= K H)) (and (= A 0) (and (exists ((var0 |tuple(uint256[],uint256[])|)) (and (and (and (and (and (exists ((var1 |tuple(uint256[],uint256[])|)) (and (and (= (|tuple(uint256[],uint256[])_accessor_0| var1) (|tuple(uint256[],uint256[])_accessor_0| var0)) (= (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr_input_0 (select (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr C) (bytes_tuple (bytes_tuple_accessor_array G) (bytes_tuple_accessor_length G)))) (|tuple(uint256[],uint256[])_accessor_0| var0))) (= (|tuple(uint256[],uint256[])_accessor_1| var1) (|tuple(uint256[],uint256[])_accessor_1| var0)))) (= (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr_input_1 (select (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr C) (bytes_tuple (bytes_tuple_accessor_array G) (bytes_tuple_accessor_length G)))) (|tuple(uint256[],uint256[])_accessor_1| var0))) (>= (bytes_tuple_accessor_length G) 0)) (>= (bytes_tuple_accessor_length H) 0)) (<= (uint_array_tuple_accessor_length (|tuple(uint256[],uint256[])_accessor_0| var0)) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (uint_array_tuple_accessor_length (|tuple(uint256[],uint256[])_accessor_0| var0)) 0))) (and (and (and (and (= (balances F) (balances F)) (= (bytes_tuple_accessor_array H) (bytes_tuple_accessor_array H))) (= (bytes_tuple_accessor_array G) (bytes_tuple_accessor_array G))) (= (bytes_tuple_accessor_length G) (bytes_tuple_accessor_length G))) (= (bytes_tuple_accessor_length H) (bytes_tuple_accessor_length H)))))))\n\
(define-fun summary_4_function_abiDecodeArray__57_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G bytes_tuple) (H bytes_tuple) (I state_type) (J bytes_tuple) (K bytes_tuple)) Bool (and (and (exists ((var0 Int)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (select (bytes_tuple_accessor_array (msg.data E)) 3) 185) (= (select (bytes_tuple_accessor_array (msg.data E)) 2) 94)) (= (select (bytes_tuple_accessor_array (msg.data E)) 1) 52)) (= (select (bytes_tuple_accessor_array (msg.data E)) 0) 205)) (= (msg.sig E) 3442761401)) (= (msg.value E) 0)) (= (state_type (store (balances F) B (+ (select (balances F) B) var0))) I)) (>= (bytes_tuple_accessor_length (msg.data E)) 4)) (<= (tx.gasprice E) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (tx.gasprice E) 0)) (<= (tx.origin E) 1461501637330902918203684832716283019655932542975)) (>= (tx.origin E) 0)) (<= (msg.sender E) 1461501637330902918203684832716283019655932542975)) (>= (msg.sender E) 0)) (<= (block.timestamp E) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (block.timestamp E) 0)) (<= (block.number E) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (block.number E) 0)) (<= (block.gaslimit E) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (block.gaslimit E) 0)) (<= (block.difficulty E) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (block.difficulty E) 0)) (<= (block.coinbase E) 1461501637330902918203684832716283019655932542975)) (>= (block.coinbase E) 0)) (<= (block.chainid E) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (block.chainid E) 0)) (<= (block.basefee E) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (block.basefee E) 0)) (>= var0 0)) (>= (- (* (- 1) (select (balances F) B)) var0) (- 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (>= (+ (select (balances F) B) var0) 0))) (exists ((var0 |tuple(uint256[],uint256[])|)) (and (and (and (and (and (exists ((var1 |tuple(uint256[],uint256[])|)) (and (and (= (|tuple(uint256[],uint256[])_accessor_0| var1) (|tuple(uint256[],uint256[])_accessor_0| var0)) (= (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr_input_0 (select (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr C) (bytes_tuple (bytes_tuple_accessor_array G) (bytes_tuple_accessor_length G)))) (|tuple(uint256[],uint256[])_accessor_0| var0))) (= (|tuple(uint256[],uint256[])_accessor_1| var1) (|tuple(uint256[],uint256[])_accessor_1| var0)))) (= (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr_input_1 (select (t_function_abidecode_pure$$returns$$_t_bytes_memory_ptr_t_array$t_uint256$dyn_memory_ptr_t_array$t_uint256$dyn_memory_ptr C) (bytes_tuple (bytes_tuple_accessor_array G) (bytes_tuple_accessor_length G)))) (|tuple(uint256[],uint256[])_accessor_1| var0))) (>= (bytes_tuple_accessor_length G) 0)) (>= (bytes_tuple_accessor_length H) 0)) (<= (uint_array_tuple_accessor_length (|tuple(uint256[],uint256[])_accessor_0| var0)) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (>= (uint_array_tuple_accessor_length (|tuple(uint256[],uint256[])_accessor_0| var0)) 0)))) (and (and (= 0 A) (= G J)) (= H K))))\n\
(define-fun summary_constructor_2_C_58_0 ((A Int) (B Int) (C abi_type) (D crypto_type) (E tx_type) (F state_type) (G state_type)) Bool (and (= G F) (and (= A 0) (and (>= (select (balances F) B) (msg.value E)) (= (balances F) (balances F))))))";
	*/
	util::h256 inputHash = util::keccak256(_input);
	if (m_queryResponses.count(inputHash))
		return m_queryResponses.at(inputHash);
	if (m_smtCallback)
	{
		auto result = m_smtCallback(ReadCallback::kindString(ReadCallback::Kind::SMTQuery), _input);
		if (result.success)
			return result.responseOrErrorMessage;
	}
	m_unhandledQueries.push_back(_input);
	return "unknown\n";
}
