// Michael Said
// Liam May
// COP 3402
// Spring 2020

// This program is a representation of a PL/0 compiler in C. It contains a Lexical
// analyzer, a parser, an intermediate code generator, and a virtual machine.
// This code takes as input a text file containing PL/0 code. It then represents
// the text as a list of lexemes and converts those lexemes into assembly code.
// That assembly code is then passed to our virtual machine to be executed.

#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdlib.h>

#define MAX_DATA_STACK_HEIGHT 40
#define MAX_IDENT_LENGTH 11
#define MAX_NUM_LENGTH 5
#define MAX_CODE_LENGTH 550
#define MAX_SYMBOL_TABLE_SIZE 500
#define MAX_LEXI_LEVELS 3
#define MAX_TYPE_LENGTH 13

typedef enum
{
  nulsym = 1, identsym = 2, numbersym = 3, plussym = 4, minussym = 5, multsym = 6,
  slashsym = 7, oddsym = 8, eqlsym = 9, neqsym = 10, lessym = 11, leqsym = 12,
  gtrsym = 13, geqsym = 14, lparentsym = 15, rparentsym = 16, commasym = 17,
  semicolonsym = 18, periodsym = 19, becomessym = 20, beginsym = 21, endsym = 22,
  ifsym = 23, thensym = 24, whilesym = 25, dosym = 26, callsym = 27, constsym = 28,
  varsym = 29, procsym = 30, writesym = 31, readsym = 32 , elsesym = 33
} token_type;

typedef struct
{
  token_type type;
  char str[MAX_TYPE_LENGTH];
}token;

typedef struct
{
  int op;
  int r;
  int l;
  int m;
}instruction;

typedef struct
{
  int kind; // const = 1, var = 2, proc = 3
  char name[12]; // name up to 11 characters
  int val; // ascii value
  int level; // L
  int addr; // M
} symbol;

token_type whatType(char *str);
bool isReserved(char *str);
bool isSymbol(char symbol);
void print_token(int tokenRep);
void print_error(int errorNum);

FILE *fpin, *fpout;
token list[MAX_CODE_LENGTH], current;
instruction ins[MAX_CODE_LENGTH];
symbol symbol_table[MAX_SYMBOL_TABLE_SIZE];
int insIndex = 0, listIndex = 0, cx;
char reserved[14][9] = { "const", "var", "procedure", "call", "begin", "end",
                         "if", "then", "else", "while", "do", "read", "write",
                         "odd" };

/////////////////////////////// End of header /////////////////////////////////

// Returns the address of a token
token *createToken(token_type t, char *str)
{
	token *tptr = malloc(1 * sizeof(token));
	tptr->type = t;
  strcpy(tptr->str, str);
	return tptr;
}

// Why does this need the file pointer if it is never used?
token getNextToken()
{
  int num;
  // token is an int representing token type
  current = list[listIndex];

  //Takes care of variables, always represented by "2 | variable"
  if (current.type == 2)
    strcpy(current.str, list[listIndex].str);
  else if (current.type == 3)
    // num is the number associated with number tokens
    num = atoi(list[listIndex].str);
    current.type = num;

  listIndex++;
  return current;
}

// Edits the string passed to it to delete all text between the '/*' and '*/'
// symbols (inclusive)
char* trim(char *str)
{
  int lp = 0, rp, diff, i, len = strlen(str);
  i = 0;
  char *trimmed = malloc(sizeof(char) * MAX_CODE_LENGTH);

  while (str[lp] != '\0')
  {
    if (str[lp] == '/' && str[lp + 1] == '*')
    {
      rp = lp + 2;
      while (str[rp] != '*' && str[rp + 1] != '/')
      {
        rp++;
      }
      lp = rp + 2;
    }
    trimmed[i] = str[lp];
    i++;
    lp++;
  }
  return trimmed;
}

// This section [will hold] the lexical analyzer and parser.
// The lexical analyzer tokenizes the code and labels the tokens as
// identifiers, reserved words, operators, and special symbols. It then checks
// for lexical errors only (order of words and symbols).
// The parser evaluates lexemes, creates a symbol table, and looks for syntax
// errors only.
int parse(char *code)
{
  token *tptr;
  int a, lp = 0, rp, length, i, lev = 0, dx = 0, tx = 0;
  char buffer[MAX_CODE_LENGTH];
  token_type t;

  // looping through string containing input and filling list of tokens
  while (code[lp] != '\0')
  {
    a = 0;

    // Ignoring whitespace
    if (isspace(code[lp]))
    {
      lp++;
    }
    if (isalpha(code[lp]))
    {
      rp = lp;

      // capturing length of substring
      while (isalpha(code[rp]) || isdigit(code[rp]))
      {
        rp++;
      }
      length = rp - lp;

      // checking for ident length error
      if (length > MAX_IDENT_LENGTH)
      {
        fprintf(fpout, "Err: ident length too long\n");
        return 0;
      }

      // creating substring
      for (i = 0; i < length; i++)
      {
        buffer[i] = code[lp + i];
      }
      buffer[i] = '\0';
      lp = rp;

      // adds reserved words to lexeme array
      if (isReserved(buffer))
      {
        t = whatType(buffer);
        tptr = createToken(t, buffer);
        list[listIndex++] = *tptr;
      }
      else
      {
        t = identsym;
        tptr = createToken(t, buffer);
        list[listIndex++] = *tptr;
      }
    }
    else if (isdigit(code[lp]))
    {
      rp = lp;

      i = 0;
      // capturing length of substring
      while (isdigit(code[lp + i]))
      {
        rp++;
        i++;
      }
      length = rp - lp;

      // Checking for ident length error
      if (length > MAX_NUM_LENGTH)
      {
        fprintf(fpout, "Err: number length too long\n");
        return 0;
      }

      // Creating substring
      for (i = 0; i < length; i++)
      {
        buffer[i] = code[lp + i];
      }
      buffer[i] = '\0';
      lp = rp;

      t = numbersym;
      tptr = createToken(t, buffer);
      list[listIndex++] = *tptr;
    }
    else if (isSymbol(code[lp]))
    {
      if (code[lp] == '+')
      {
        t = 4;
      }
      if (code[lp] == '-')
      {
        t = 5;
      }
      if (code[lp] == '*')
      {
        t = 6;
      }
      if (code[lp] == '/')
      {
        t = 7;
      }
      if (code[lp] == '(')
      {
        t = 15;
      }
      if (code[lp] == ')')
      {
        t = 16;
      }
      if (code[lp] == '=')
      {
        t = 9;
      }
      if (code[lp] == ',')
      {
        t = 17;
      }
      if (code[lp] == '.')
      {
        t = 19;
      }
      if (code[lp] == '<')
      {
        t = 11;
        if(code[lp+1] == '>')
        {
          t = 10;
          a = 1;
        }

        if(code[lp+1] == '=')
        {
          t = 12;
          a = 1;
        }
      }
      if (code[lp] == '>')
      {
        t = 13;
        if(code[lp+1] == '=')
        {
          t = 14;
          a = 1;
        }
      }
      if (code[lp] == ';')
      {
        t = 18;
      }
      if (code[lp] == ':')
      {
        // We can assume : is always followed by =
        t = 20;
        a = 1;
      }
      else
      {
        fprintf(fpout, "Err: Invalid symbol\n");
        return 0;
      }

      buffer[0] = code[lp];
      buffer[1] = '\0';
      if (a = 1)
      {
        buffer[2] = '\0';
        buffer[1] = code[++lp];
      }
      tptr = createToken(t, buffer);
      list[listIndex++] = *tptr;
      lp++;
    }
  }
  free(tptr);
  return listIndex;
}

// program description
void program(symbol* symbol_table, instruction* code)
{
  current = getNextToken();
  block(0,0, symbol_table, code);
  if(current != periodsym)
  {
    print_error(9);
  }
}

// block description
void block(int level, int tableIndex, symbol* symbol_table)
{
  if(MAX_LEXI_LEVELS < level)
  {
    findError(26);
  }

  int dataIndex = 4, tableIndex2, cx2;
  tableIndex2 = tableIndex;
  symbol_table[tableIndex].addr = cx;
  emit(7,0,0, code);



   while( (current == constsym) || (current == varsym) || (current == procsym) )
   {
       if (current == constsym)
       {
           current = getNextToken();
            while (current == identsym)
            {
               constdeclaration(level, &tableIndex, &dataIndex, symbol_table);
               while(current == commasym)
               {
                   current = getNextToken();
                   constdeclaration(level, &tableIndex, &dataIndex, symbol_table);
               }
               if(current == semicolonsym) {
                   current = getNextToken();
               }
               else
               {
                   print_error(5);
               }
           }
       }
       if (current == varsym)
       {
           current = getNextToken();
           while(current == identsym)
           {
               vardeclaration(level, &tableIndex, &dataIndex, symbol_table);
               while (token == commasym)
               {
                   current = getNextToken();
                   vardeclaration(level, &tableIndex, &dataIndex, symbol_table);
               }
               if(current == semicolonsym)
               {
                   current = getNextToken();
               }
               else
               {
                   print_error(5);
               }
           }
       }
       while(current == procsym)
       {
           current = getNextToken();

           if(current == identsym)
           {
               enter(3, &tableIndex, &dataIndex, level, symbol_table);
               current = getNextToken();
           }
           else
           {
               print_error(4);
           }
           if(current == semicolonsym)
           {
               current = getNextToken(ifp);
           }
           else
           {
               print_error(5);
           }

           block(level+1, tableIndex, tableIndex, code);
           if(current == semicolonsym)
           {
               current = getNextToken();
           }
           else
           {
               print_error(5);
           }
           }
      }
   code[symbol_table[tableIndex2].addr].m = cx;
   symbol_table[tableIndex2].addr = cx;
   cx2 = cx;
   //6 = inc
   emit(6, 0, dataIndex, code);
   statement(level, &tableIndex, code, symbol_table);
   emit(2, 0, 0, code);
}

// Statement
void statement(int lev, int *ptx)
{
  int i, cx1, cx2;
  if (current.type == identsym)
  {
    i = position(current.str, ptx, symbol_table, lev);
    if (i == 0)
    {
      print_error(11); //Undeclared identifier.
    }
    else if (symbol_table[i].kind != 2)
    {
      print_error(12); //Assignment to constant or procedure is not allowed
      i = 0;
    }
    current = getNextToken();
    if (current.type == becomessym)
    {
      current = getNextToken();
    }
    else
    {
      print_error(13); //Assignment operator expected.
    }
    expression(lev, ptx, ins, symbol_table);
    if (i != 0)
    {
      emit(4, lev-table[i].level, table[i].addr, ins); // 4 is STO for op, lev-table[i].level is for L, table[i].adr for M
      // I don't know what his lev-table is but I think whatever he is doing
      // with it, we can implement it in a better way
    }
  }
  else if (current.type == callsym)
  {
    current = getNextToken();
    if (token != identsym)
    {
      print_error(14); //call must be followed by an identifier
    }
    else
    {
      i = position(current.str, ptx, symbol_table, lev);
      if(i == 0)
      {
        print_error(11); //Undeclared identifier.
      }
      else if (table[i].kind==3)
      {//proc
        emit(5,lev-table[i].level, table[i].addr, ins); // 5 is CAL for op, lev-table[i].level is for L, table[i].adr for M
          //statement::= ["call" ident | ...]
      }
      else
      {
        print_error(15); //Call of a constant or variable is meaningless
      }
      current = getNextToken();
    }
  }
  else if (current.type == ifsym)
  {
    current = getNextToken();
    condition(lev, ptx, ins, symbol_table);
    if (current.type == thensym)
    {
      current = getNextToken();
    }
    else
    {
      print_error(16);  // then expected
    }

    cx1 = cx;
    emit(8, 0, 0, ins); // 8 is JPC for op, 0 is for L and 0 for M
    statement(lev, ptx, ins, symbol_table);

    /**working on else**/
    if (current.type == elsesym)
    {
      current = getNextToken();

      code[cx1].m = cx+1; //jumps past if
      cx1 = cx;
      emit(7, 0, 0, ins); // 7 is JMP for op, 0 is for L and cx1 for M
      //updates JPC M value
      statement(lev, ptx, ins, symbol_table);
    }
    code[cx1].m = cx; //jumps past else (if theres an else statement) otherwise jumps past if
  }

  //begin <condition> end <statement>
  else if (current.type == beginsym)
  {
    current = getNextToken();
    statement(lev, ptx, ins, symbol_table);

     /**changed**/
     while (current.type == semicolonsym)
     {
       current = getNextToken();
       statement(lev, ptx, ins, symbol_table);
     }

    /**original**/
    /*while((token==semicolonsym)||(token==beginsym)||
     (token==ifsym)||(token==elsesym)||(token==whilesym)||
          (token==callsym)||(token==writesym)||(token==readsym)) {
        if (token==semicolonsym) {
            token = getNextToken();
        }
        else {
            error(10);  //Semicolon between statements missing.
        }
        statement(lev,ptx, ifp, code, table);
    }*/ //end original
    if (current.type == endsym)
    {
      current = getNextToken();
    }
    else
    {
      print_error(17);  //Semicolon or } expected.
    }
  }

  //while <condition> do <statement>
  else if (current.type == whilesym)
  {
    cx1 = cx;
    current = getNextToken();
    condition(lev, ptx, ins, symbol_table);
    cx2 = cx;
    emit(8, 0, 0, ins); // 8 is JPC for op, 0 is for L and 0 for M
    if (current.type == dosym)
    {
      current = getNextToken();
    }
    else
    {
      print_error(18);  // do expected
    }
    statement(lev, ptx, ins, symbol_table);
    emit(7, 0, cx1, ins); // 7 is JMP for op, 0 is for L and cx1 for M, jump to instruction cx1
    code[cx2].m = cx;
  }

  //write needs to write
  else if (current.type == writesym)
  {
    current = getNextToken();
    expression(lev, ptx, ifp, code, table);
    emit(9,0,1, code); // 9 is SIO1 for op, 0 is for L and 1 for M, write the top stack element to the screen
  }
  //read needs to read and STO
  else if (current.type == readsym)
  {
    current = getNextToken();
    emit(10, 0, 2, code); // 10 is SIO2 for op, 0 is for L and 1 for M, write the top stack element to the screen
    i=position(current.str, ptx, symbol_table, lev);
    if (i == 0)
    {
      print_error(11); //Undeclared identifier.
    }
    else if (symbol_table[i].kind != 2)
    { //var
      print_error(12); //Assignment to constant or procedure is not allowed
      i = 0;
    }
    if (i != 0)
    {
      emit(4, lev-table[i].level, table[i].addr, code); // 4 is STO for op, lev-table[i].level is for L, table[i].adr for M
    }
     current = getNextToken();
  }
}

// condition description
void condition(int level, int* ptableindex, instruction* code, symbol* symbol_table)
{

  if( current == oddsym)
  {
    current = getNextToken();
    expression(level, ptableindex, code, symbol_table);
    emit(2, 0, 6, code);
  }

  int rel_switch;
  else
  {
    expression(level, ptableindex, code, symbol_table);
    if( (current != eqsym) && ( current != neqsym) && (current != lessym) && ( current !=leqsym) && ( current != gtrsym) && (current != geqsym) )
    {
      print_error(20);
    }

    else
    {
      rel_switch = current;
      current = getNextToken();
      expression(level, ptableindex, code, symbol_table);

      if(rel_switch == 9)
      {
        emit(2,0,8, code);
      }
      if(rel_switch == 10)
      {
        emit(2,0,9, code);
      }
      if(rel_switch == 11)
      {
        emit(2,0,10, code);
      }
      if(rel_switch == 12)
      {
        emit(2,0,11, code);
      }
      if(rel_switch == 13)
      {
        emit(2,0,12, code);
      }
      if(rel_switch == 14)
      {
        emit(2,0,13, code);
      }
    }
}

// expression explanation
void expression(int lev, int *ptx)
{
  int addop;
  if (current.type == plussym || current.type == minussym)
  {
    addop = current.type;
    current = getNextToken();
    term(lev, ptx, ifp, code, table);
    if(addop == minussym)
      emit(2, 0, 1, code); // 2 is OPR for op, 1 is NEG for M inside OPR
  }
  else
  {
    term (lev, ptx, ifp, code, table);
  }
  while (token == plussym || token == minussym)
  {
    addop = token;
    token = getNextToken();
    term(lev, ptx, ifp, code, table);
    if (addop == plussym)
    {
      emit(2, 0, 2, code); // 2 is OPR for op, 2 is ADD for M inside OPR
    }
    else
    {
      emit(2, 0, 3, code); // 2 is OPR for op, 3 is SUB for M inside OPR
    }
  }
}

// term explanation
void term(int lev, int *ptx, FILE* ifp, instruction* code, symbol* table)
{
  int mulop;
  factor(lev, ptx, table, ifp, code);
  while(token == multsym || token == slashsym)
  {
    mulop = current.type;
    current.type = getNextToken(ifp);
    factor(lev, ptx, table, ifp, code);
    if(mulop == multsym)
    {
      emit(2, 0, 4, code); // 2 is OPR for op, 4 is MUL for M inside OPR
    }
    else
    {
      emit(2, 0, 5, code); // 2 is OPR for op, 5 is DIV for M inside OPR
    }
  }
}

// factor explanation
void factor(int lev, int *ptx)
{
  int i, level, adr, val;

  while ((current.type == identsym) || (current.type == numbersym) || (current.type == lparentsym))
  {
    if (current.type == identsym)
    {
      i = position(id,ptx, table, lev);
      if (i == 0)
      {
        print_error(11); // undeclared identifier
      }
      else
      {
        kind = table[i].kind;
        level = table[i].level;
        adr = table[i].addr;
        val = table[i].val;
        if (kind == 1)
        {//const
          emit(1,0,val, code); // 1 is LIT for op, val is for M inside LIT
        }
        else if (kind==2)
        {//var
          emit(3,lev-level,adr, code); // 3 is LOD for op, lev-level is L inside LOD, adr is for M inside LOD
        }
        else
        {
          error(21); // Expression must not contain a procedure identifier
        }
      }
      current.type = getNextToken();
    }
    /***this might need to be changed***/
    else if (token == numbersym)
    {
      if (num > 2047)
      { //maximum address
        print_error(25);
        num = 0;
      }
      emit(1,0,num, code); // 1 is LIT for op, num is for M inside LIT
      current.type = getNextToken();
    }
    else if (current.type == lparentsym)
    {
      token = getNextToken();
      expression(lev,ptx, ifp, code, table);
      if (current.type == rparentsym)
      {
        token = getNextToken(ifp);
      }
      else
      {
        print_error(22); // Right parenthesis missing.
      }
    }
  }
}

// Returns true if the character sent is a valid symbol or false otherwise
bool isSymbol(char symbol)
{
  char validsymbols[13] = {'+', '-', '*', '/', '(', ')', '=', ',', '.', '<', '>',  ';', ':'};

  for (int i = 0; i < 13; i++)
  {
    if(symbol == validsymbols[i])
    {
      return true;
    }
  }
  return false;
}

// Returns true if string is a valid number and false otherwise
bool isNumber(char *str)
{
  int i, len = strlen(str);

  if (len > MAX_NUM_LENGTH)
  {
    return false;
  }
  for (i = 0; i < len; i++)
  {
    if (!isdigit(str[i]))
    {
      return false;
    }
  }
  return true;
}

// Returns true if the string is a reserved keyword and false otherwise
bool isReserved(char *str)
{
  if (str[0] == 'b')
  {
    if (strcmp(reserved[4], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 'c')
  {
    if (strcmp(reserved[0], str) == 0)
    {
      return true;
    }
    else if (strcmp(reserved[3], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 'd')
  {
    if (strcmp(reserved[10], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 'e')
  {
    if (strcmp(reserved[5], str) == 0)
    {
      return true;
    }
    else if (strcmp(reserved[8], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 'i')
  {
    if (strcmp(reserved[6], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 'o')
  {
    if (strcmp(reserved[13], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 'p')
  {
    if (strcmp(reserved[2], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 'r')
  {
    if (strcmp(reserved[11], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 't')
  {
    if (strcmp(reserved[7], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 'v')
  {
    if (strcmp(reserved[1], str) == 0)
    {
      return true;
    }
  }
  if (str[0] == 'w')
  {
    if (strcmp(reserved[9], str) == 0)
    {
      return true;
    }
    else if (strcmp(reserved[12], str) == 0)
    {
      return true;
    }
  }
  return false;
}

// Given a string, determines if that string represents a type of token and if so,
// returns the value of that token
token_type whatType(char *str)
{
  if (str[0] == 'b')
  {
    if (strcmp(reserved[4], str) == 0)
    {
      return 21;
    }
  }
  if (str[0] == 'c')
  {
    if (strcmp(reserved[0], str) == 0)
    {
      return 28;
    }
    else if (strcmp(reserved[3], str) == 0)
    {
      return 27;
    }
  }
  if (str[0] == 'd')
  {
    if (strcmp(reserved[10], str) == 0)
    {
      return 26;
    }
  }
  if (str[0] == 'e')
  {
    if (strcmp(reserved[5], str) == 0)
    {
      return 22;
    }
    else if (strcmp(reserved[8], str) == 0)
    {
      return 33;
    }
  }
  if (str[0] == 'i')
  {
    if (strcmp(reserved[6], str) == 0)
    {
      return 23;
    }
  }
  if (str[0] == 'o')
  {
    if (strcmp(reserved[13], str) == 0)
    {
      return 8;
    }
  }
  if (str[0] == 'p')
  {
    if (strcmp(reserved[2], str) == 0)
    {
      return 30;
    }
  }
  if (str[0] == 'r')
  {
    if (strcmp(reserved[11], str) == 0)
    {
      return 32;
    }
  }
  if (str[0] == 't')
  {
    if (strcmp(reserved[7], str) == 0)
    {
      return 24;
    }
  }
  if (str[0] == 'v')
  {
    if (strcmp(reserved[1], str) == 0)
    {
      return 29;
    }
  }
  if (str[0] == 'w')
  {
    if (strcmp(reserved[9], str) == 0)
    {
      return 25;
    }
    else if (strcmp(reserved[12], str) == 0)
    {
      return 31;
    }
  }
  // If the input does not match any of our reserved words, returns the nulsym
  return 1;
}

// Prints data to output file as requested by command line arguments
void output(int count, bool l, bool a, bool v)
{
  int i = 0;
  char buffer[13] = {'\0'};

  // In the absence of commands, just printing "in" and "out"
  if (l == false && a == false && v == false)
  {
    fprintf(fpout, "in\tout\n");
    return;
  }

  // If commanded to print list of lexemes, printing all elements of list and
  // their symbol type (from token_type)
  if (l == true)
  {
    fprintf(fpout, "List of lexemes:\n\n");
    for(int i=0; i<count; i++)
    {
      fprintf(fpout, "%d ", list[i].type);
      if(list[i].type == 2 || list[i].type == 3)
      {
        fprintf(fpout, "%s ", list[i].str);
      }
    }
    fprintf(fpout, "\n\nSymbolic representation:\n\n");
    for (i = 0; i < count; i++)
    {
      // call print to convert number to string
      print_token(list[i].type);
      (i % 10 == 0) ? fprintf(fpout, "\n") : fprintf(fpout, "\t");
    }
    fprintf(fpout, "\n\nNo errors, program is syntactically correct\n\n");
  }

  // If commanded to print generated assembly code, printing all elements of ins
  if (a == true)
  {
    i = 0;
    //while((ins[i].op != 0 && ins[i].r != 0 && ins[i].l !=0 && ins[i].m !=0)) // <--- not ever entering loop because ins[] never gets filled ???
    for(int i=0; i<1000; i++)
    {
      fprintf(fpout, "%d %d %d %d \n", ins[i].op, ins[i].r, ins[i].l, ins[i].m);
      //i++;
    }
  }

  if (v == true)
  {
    // Converting instruction array to int array
    int code[MAX_CODE_LENGTH];
    for (i = 0; i < insIndex; i++)
    {
      code[i + 1] = ins[i].op;
      code[i + 2] = ins[i].r;
      code[i + 3] = ins[i].l;
      code[i + 4] = ins[i].m;
    }

    // Printing generated code
    for (i = 0; i < insIndex; i++)
    {
      fprintf(fpout, "%d", code[i]);
      (i % 4 == 0) ? fprintf(fpout, "\n") : fprintf(fpout, "\t");
    }

    // Printing virtual machine execution trace
    // print_stack(code, insIndex);
    // executionCycle(code);
  }
}

// Prints a unique error message for each error code
void print_error(int errorNum)
{
  switch( errorNum )
  {
    case 1:
      printf("Use = instead of := \n");
      break;

    case 2:
      printf("= must be followed by a number \n");
      break;

    case 3:
      printf("Identifier must be followed by = \n");
      break;

    case 4:
      printf("const, int, procedure must be followed by identifier\n");
      break;

    case 5:
      printf("Semicolon or comma missing\n");
      break;

    case 6:
      printf("Incorrect symbol after procedure declaration\n");
      break;

    case 7:
      printf("Statement expected\n");
      break;

    case 8:
      printf("Incorrect symbol after statement part in block\n");
      break;

    case 9:
      printf("Period expected\n");
      break;

    case 10:
      printf("Semicolon between statements missing\n");
      break;

    case 11:
      printf("Undeclared identifier \n");
      break;

    case 12:
      printf("Assignment to constant or procedure is not allowed\n");
      break;

    case 13:
      printf("Assignment operator expected\n");
      break;

    case 14:
      printf("Call must be followed by an identifier\n");
      break;

    case 15:
      printf("Call of a constant or variable is meaningless\n");
      break;

    case 16:
      printf("Then expected\n");
      break;

    case 17:
      printf("Semicolon or } expected \n");
      break;

    case 18:
      printf("Do expected\n");
      break;

    case 19:
      printf("Incorrect symbol following statement\n");
      break;

    case 20:
      printf("Relational operator expected\n");
      break;

    case 21:
      printf("Expression must not contain a procedure identifier\n");
      break;

    case 22:
      printf("Right parenthesis missing\n");
      break;

    case 23:
      printf("The preceding factor cannot begin with this symbol\n");
      break;

    case 24:
      printf("An expression cannot begin with this symbol\n");
      break;

    case 25:
      printf("This number is too large\n");
      break;

    default:
    printf("Invalid instruction");
  }
}

// Given the value of token symbol, prints the type of token symbol
void print_token(int tokenRep)
{
  switch (tokenRep)
  {
    case 1: fprintf(fpout, "nulsym");
      break;
    case 2: fprintf(fpout, "identsym");
      break;
    case 3: fprintf(fpout, "numbersym");
      break;
    case 4: fprintf(fpout, "plussym");
      break;
    case 5: fprintf(fpout, "minussym");
      break;
    case 6: fprintf(fpout, "multsym");
      break;
    case 7: fprintf(fpout, "slashsym");
      break;
    case 8: fprintf(fpout, "oddsym");
      break;
    case 9: fprintf(fpout, "eqlsym");
      break;
    case 10: fprintf(fpout, "neqsym");
      break;
    case 11: fprintf(fpout, "lessym");
      break;
    case 12: fprintf(fpout, "leqsym");
      break;
    case 13: fprintf(fpout, "gtrsym");
      break;
    case 14: fprintf(fpout, "geqsym");
      break;
    case 15: fprintf(fpout, "lparentsym");
      break;
    case 16: fprintf(fpout, "rparentsym");
      break;
    case 17: fprintf(fpout, "commasym");
      break;
    case 18: fprintf(fpout, "semicolonsym");
      break;
    case 19: fprintf(fpout, "periodsym");
      break;
    case 20: fprintf(fpout, "becomessym");
      break;
    case 21: fprintf(fpout, "beginsym");
      break;
    case 22: fprintf(fpout, "endsym");
      break;
    case 23: fprintf(fpout, "ifsym");
      break;
    case 24: fprintf(fpout, "thensym");
      break;
    case 25: fprintf(fpout, "whilesym");
      break;
    case 26: fprintf(fpout, "dosym");
      break;
    case 27: fprintf(fpout, "callsym");
      break;
    case 28: fprintf(fpout, "constsym");
      break;
    case 29: fprintf(fpout, "varsym");
      break;
    case 30: fprintf(fpout, "procsym");
      break;
    case 31: fprintf(fpout, "writesym");
      break;
    case 32: fprintf(fpout, "readsym");
      break;
    case 33: fprintf(fpout, "elsesym");
      break;
  }
}

int main(int argc, char **argv)
{
  fpin = fopen(argv[1], "r");
  fpout = fopen(argv[2], "w+");
  char aSingleLine[MAX_CODE_LENGTH], code[MAX_CODE_LENGTH] = {'\0'},
       trimmed[MAX_CODE_LENGTH] = {'\0'}, commands[3][3], c;
  int count, i, tokens[MAX_SYMBOL_TABLE_SIZE] = {'\0'};
  token current;
  bool l = false, a = false, v = false;

  // In case user doesn't know how to use program
  if (argc < 3 || argc > 6)
  {
    printf("Err: incorrect number of arguments\nTo use compiler, type: ./a.out <inputfilename.txt> <outputfilename.txt> <up to one of each of the following commands: -l -a -v>\n");
    return 0;
  }
  if (argc == 4)
  {
    strcpy(commands[0], argv[3]);
  }
  if (argc == 5)
  {
    strcpy(commands[0], argv[3]);
    strcpy(commands[1], argv[4]);
  }
  if (argc == 6)
  {
    strcpy(commands[0], argv[3]);
    strcpy(commands[1], argv[4]);
    strcpy(commands[2], argv[5]);
  }
  for (i = 0; i < (argc - 3); i++)
  {
    if (strcmp(commands[i], "-l") == 0)
      l = true;
    if (strcmp(commands[i], "-a") == 0)
      a = true;
    if (strcmp(commands[i], "-v") == 0)
      v = true;
  }

  // Initializing lexeme list
  for (i = 0; i < MAX_CODE_LENGTH; i++)
  {
    list[i].type = nulsym;
    list[i].str[0] = '\0';
  }

  // Preventing segfault by checking for failures to open files
  if (fpin == NULL)
  {
    printf("File not found\n");
    return 0;
  }
  if (fpout == NULL)
  {
    printf("File not found\n");
    return 0;
  }

  // Scanning file into code array
  while(fgets(aSingleLine, MAX_CODE_LENGTH, fpin))
  {
    strcat(code, aSingleLine);
  }

  // Removing all comments from code
  strcpy(code, trim(code));

  // Filling lexeme array and capturing number of elements of lexeme array
  // (or 0 if parse found errors)
  count = parse(code);

  if (count == 0)
  {
    fprintf(fpout, "Error(s), program is not syntactically correct\n");
    return 0;
  }

  printf("\n\n%s\n\n", code); // debugging
  // Printing output
  output(count, l, a, v);

  fclose(fpin);
  fclose(fpout);
  return 0;
}
