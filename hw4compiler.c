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

FILE *fpin, *fpout;
token list[MAX_CODE_LENGTH];
instruction ins[MAX_CODE_LENGTH];
symbol symbol_table[MAX_SYMBOL_TABLE_SIZE];
int ins_cntr = 0;
char reserved[14][9] = { "const", "var", "procedure", "call", "begin", "end",
                         "if", "then", "else", "while", "do", "read", "write",
                         "odd" };

/////////////////////////////// End of header /////////////////////////////////

// Returns the address of a lexeme
token *createToken(token_type t, char *str)
{
	token *tptr = malloc(1 * sizeof(token));
	tptr->type = t;
  strcpy(tptr->str, str);
	return tptr;
}

// Edits the string passed to it to delete all text between the '/*' and '*/'
// symbols (inclusive)
char* trim(char *str)
{
  int lp = 0, rp, diff, i, len = strlen(str);
  i=0;
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
      lp = rp;
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
  int lp = 0, rp, length, i, listIndex = 0;
  char buffer[MAX_CODE_LENGTH];
  token_type t;

  // looping through string containing input
  while (code[lp] != '\0')
  {
    int a = 0;
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
        printf("Err: ident length too long\n");
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
        printf("Err: number length too long\n");
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
    // Creating a lexeme for the symbol//call createlex w t and sym
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
        if(code[lp+1] == '>')
        {
          t = 10;
          a=1;
        }

        if(code[lp+1] == '=')
        {
          t = 12;
          a=1;
        }
        t = 11;
      }
      if (code[lp] == '>')
      {
        if(code[lp+1] == '=')
        {
          t = 14;
          a=1;
        }
        t = 13;
      }
      if (code[lp] == ';')
      {
        t = 18;
      }
      if (code[lp] == ':')
      {
        if(code[lp+1] == '=')
        {
          t = 20;
          a=1;
        }
        t = 20;
      }

      buffer[0] = code[lp];
      buffer[1] = '\0';
      tptr = createToken(t, buffer);
      list[listIndex++] = *tptr;
      lp++;
    }
  }
  free(tptr);
  return listIndex;
}

void program(symbol* symbol_table, instruction* code)
{
  current = getNextToken();
  block(0,0, symbol_table, code);
  if(current != periodsym)
  {
    print_error(9);
  }
}

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
}}


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
    for (i = 0; i < count; i++)
    {
      fprintf(fpout, "%s", list[i].str);
      (i % 10 == 0) ? fprintf(fpout, "\n") : fprintf(fpout, "\t");
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
    for (i = 0; i < ins_cntr; i++)
    {
      code[i + 1] = ins[i].op;
      code[i + 2] = ins[i].r;
      code[i + 3] = ins[i].l;
      code[i + 4] = ins[i].m;
    }

    // Printing generated code
    for (i = 0; i < ins_cntr; i++)
    {
      fprintf(fpout, "%d", code[i]);
      (i % 4 == 0) ? fprintf(fpout, "\n") : fprintf(fpout, "\t");
    }

    // Printing virtual machine execution trace
    // print_stack(code, ins_cntr);
    // executionCycle(code);
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
       trimmed[MAX_CODE_LENGTH] = {'\0'}, commands[3][3];
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
  while(!feof(fpin))
  {
    fgets(aSingleLine, MAX_CODE_LENGTH, fpin);
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

  // Printing output
  output(count, l, a, v);

  fclose(fpin);
  fclose(fpout);
  return 0;
}

