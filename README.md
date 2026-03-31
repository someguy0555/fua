# BNF
```EBNF

<expr>       := equality;
<equality>   := comparison ( ( "==" "!=" ) comparison )*;
<comparison> := logical ( ( "<" "<=" ">" ">=" ) logical )*;
<logical>    := term ( ( "&&" "||" ) term )*;
<term>       := factor ( ( "+" "-" ) factor)*;
<factor>     := unary ( ( "*" "/" "%" ) unary )*;
<unary>      := ( "!" | "-" ) unary | primary;
<primary>    := <number> | <identifier> | "(" <expr> ")";


```
