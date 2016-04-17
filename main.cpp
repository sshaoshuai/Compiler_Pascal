#include <iostream>
#include <cstdio>
#include <stdlib.h>
#include <string.h>
#include <vector>
#include <stack>
#include <map>

#define AND     1
#define ARRAY   2
#define BEGIN   3
#define CASE    4
#define CONST   5
#define DIV     6
#define DO      7
#define DOWNTO  8
#define ELSE    9
#define END     10
#define P_FILE  11
#define FOR     12
#define FUNC    13
#define GOTO    14
#define IF      15
#define IN      16
#define LABEL   17
#define MOD     18
#define NIL     19
#define NOT     20
#define OF      21
#define OR      22
#define PACKED  23
#define PROC    24
#define PROG    25
#define RECORD  26
#define REPEAT  27
#define SET     28
#define THEN    29
#define TO      30
#define TYPE    31
#define UNTIL   32
#define VAR     33
#define WHILE   34
#define WITH    35
#define ID      36
#define INT     37
#define REAL    38
#define STRING  39
#define PLUS    40
#define MINUS   41
#define MULTI   42
#define RDIV    43
#define EQ      44
#define LT      45
#define GT      46
#define LE      47
#define GE      48
#define NE      49
#define LR_BRAC 50
#define RR_BRAC 51
#define COMMA   52
#define P_MARK  53
#define F_STOP  54
#define RANGE   55
#define COLON   56
#define ASSIGN  57
#define SEMIC   58
#define CAP     59
#define EXP     60
#define LS_BRAC 61
#define RS_BRAC 62
#define Q_MARK  63

#define INTEGER  64
#define REALTYPE 65
#define RELOP    45

using namespace std;
typedef pair<int, void*> TokenPairType;

// �ֵ����ڵ�ṹ����
struct TrieNode{
    char ch;
    int  code_of_kind;
    void * pos;
    TrieNode * next[256];
    TrieNode(){
        code_of_kind = -1;
        memset(next, 0, sizeof(next));
    }
    TrieNode(char _ch){
        ch = _ch; code_of_kind = -1;
        memset(next, 0, sizeof(next));
    }
};
TrieNode * root = new TrieNode('*');

map<string, int> sign_to_num;   // ���ս���ͱ���ת��Ϊ����  �ս��-�� | ����-��

const int BUFFER_LEN = 100;                     // ���뻺������С
const char * src_file = "data_for_syntax.pas";                // �����ļ�·��
const char * out_file = "word_stream.txt";         // ����ļ�·��
const char * LR1_table = "LR1_table.htm";              // LR1������
FILE *fp_srcfile = NULL;                        // �����ļ�ָ��
FILE *fp_outfile = NULL;                        // ����ļ�ָ��

// �ʷ���������
class LexicoAnalyzer{
    char *src_data;                    // Դ����ָ��
    char *read_buffer;                 // ���뻺���������ô���ǵ�˫������ʵ��
    char *word_now;                    // ����ʻ�ʱ��ǰָ��
    char *bufferA_end, *bufferB_end;   // �������������ұ߽�ָ��
    char stack_buf[BUFFER_LEN];        // ģ����˻���ջ
    char token_buf[BUFFER_LEN];        // ʶ�� token ʱ�ݴ���
    int  file_len, stack_buf_top, token_buf_cnt;
    int  is_taking_string, row_cnt, file_end, string_cnt;
public:
    // ���캯�������ڴʷ��������ĳ�ʼ��
    LexicoAnalyzer(){
        // ����ǵ�˫�������ĳ�ʼ��, 0-49, EOF(50), 51-100, EOF
        read_buffer = (char * ) malloc(BUFFER_LEN + 2);
        bufferA_end = read_buffer + BUFFER_LEN / 2;
        bufferB_end = read_buffer + BUFFER_LEN + 1;
        *bufferA_end = EOF; *bufferB_end = EOF;
        word_now = read_buffer - 1;

        string_cnt = stack_buf_top = is_taking_string = file_end = 0;
        row_cnt = 1;
    }

    void error_handle(int type_of_error, const char *src_error, char ch){
        switch (type_of_error){
            case 1:
                printf("row %d: Number Format Error! --> %s\n", row_cnt, src_error);
                break;
            case 2:
                printf("row %d: Number Format Error! --> %s\n", row_cnt, src_error);
                break;
            case 4:
                printf("row %d: String Is Too Long! --> %s\n", row_cnt, src_error);
                break;
            case 3:
                printf("row %d: Invalid Char --> %c\n", row_cnt, ch);
                break;
            default:
                printf("row %d: Unknown Error!\n", row_cnt);
        }
    }
    // ��ȡ�����ļ���������
    void ReadFile(){
        fp_srcfile = fopen(src_file, "r");
        if(fp_srcfile == NULL){
            printf("open file error: %s\n", src_file);
            exit(0);
        }
        fseek(fp_srcfile, 0, SEEK_END);
        file_len = ftell(fp_srcfile);
        src_data = (char *)malloc(file_len + 6);
        fseek(fp_srcfile, 0, SEEK_SET);
        fread(src_data, file_len, 1, fp_srcfile);

        printf("%s###\n", src_data);
        printf("%d\n", file_len);
        fclose(fp_srcfile);
    }
    //���ݵ�ǰ�ַ���ȡ�� trie ���� next �±�
    int get_trie_index(char ch){
        if(ch >= 'A' && ch <= 'Z')
            return ch - 'A' + 'a';
        return ch;
    }

    // �� Trie ���л�ȡ��ǰ��㣬���û�оͲ���ڵ㣬��������ڵ��ָ��
    TrieNode *get_from_trie(const char * word){
        TrieNode * now = root;
        for(int i = 0; word[i] != '\0'; i++){
            if(now->next[get_trie_index(word[i])] == NULL){
                now->next[get_trie_index(word[i])] = new TrieNode(word[i]);
            }
            now = now->next[get_trie_index(word[i])];
        }
        return now;
    }
    // ����ǰ�ؼ��ֲ��뵽 Trie ����
    void install_keyword(const char * keyword, int code_of_kind){
        TrieNode * now = get_from_trie(keyword);
        now->code_of_kind = code_of_kind;

        sign_to_num[string(keyword)] = code_of_kind;    // ���ս��ӳ����ӵ�ת������
    }
    // Ԥ����������keyword���뵽 Trie ����
    void update_keyword_in_trie(){
        sign_to_num.clear();
        // ��������
        install_keyword("id", ID);          install_keyword("semi", SEMIC);
        install_keyword("digits", INT);     install_keyword("integer", INTEGER);
        install_keyword("real", REALTYPE);  install_keyword("assignop", ASSIGN);
        install_keyword("relop", RELOP);    install_keyword("addop", PLUS);
        install_keyword("mulop", MULTI);    install_keyword("num", INT);

//        const char * T_sign[T_NUM] = {
//            "prog", "id", "(", ")", "semi", ",", "var", ":", "digits", "..", "of",
//            "array", "integer", "real", "[", "]", "begin", "end", "function",
//            "procedure", "if", "then", "else", "while", "do", "assignop", "relop",
//            "addop", "mulop", "num", "not", "+", "-", "a", "b", "$"
//        };   // �洢�����ս��

        // ������
        install_keyword("and",      AND);   install_keyword("array",    ARRAY);
        install_keyword("begin",    BEGIN); install_keyword("case",     CASE);
        install_keyword("const",    CONST); install_keyword("div",      DIV);
        install_keyword("do",       DO);    install_keyword("downto",   DOWNTO);
        install_keyword("else",     ELSE);  install_keyword("end",      END);
        install_keyword("file",     P_FILE);install_keyword("for",      FOR);
        install_keyword("function", FUNC);  install_keyword("goto",     GOTO);
        install_keyword("if",       IF);    install_keyword("in",       IN);
        install_keyword("label",    LABEL); install_keyword("mod",      MOD);
        install_keyword("nil",      NIL);   install_keyword("not",      NOT);
        install_keyword("of",       OF);    install_keyword("or",       OR);
        install_keyword("packed",   PACKED);install_keyword("procedure",PROC);
        install_keyword("prog",     PROG);  install_keyword("record",   RECORD);
        install_keyword("repeat",   REPEAT);install_keyword("set",      SET);
        install_keyword("then",     THEN);  install_keyword("to",       TO);
        install_keyword("type",     TYPE);  install_keyword("until",    UNTIL);
        install_keyword("var",      VAR);   install_keyword("while",    WHILE);
        install_keyword("with",     WITH);
        // ����
        install_keyword("+",    PLUS);      install_keyword("+",        PLUS);
        install_keyword("-",    MINUS);     install_keyword("*",        MULTI);
        install_keyword("/",    RDIV);      install_keyword("=",        EQ);
        install_keyword("<",    LT);        install_keyword(">",        GT);
        install_keyword("<=",   LE);        install_keyword(">=",       GE);
        install_keyword("<>",   NE);        install_keyword("(",        LR_BRAC);
        install_keyword(")",    RR_BRAC);   install_keyword(",",        COMMA);
        install_keyword(".",    F_STOP);    install_keyword("..",       RANGE);
        install_keyword(":",    COLON);     install_keyword(":=",       ASSIGN);
        install_keyword(";",    SEMIC);     install_keyword("^",        CAP);
        install_keyword("**",   EXP);       install_keyword("[",        LS_BRAC);
        install_keyword("]",    RS_BRAC);   install_keyword("'",       Q_MARK);

    }
    // �ӻ�������ȡ�ַ������˫��������ά��
    char getchar_from_buffer(){
        if(stack_buf_top > 0){
            token_buf[token_buf_cnt++] = stack_buf[--stack_buf_top];
            return token_buf[token_buf_cnt - 1];
        }
        if(*(++word_now) != EOF){
            token_buf[token_buf_cnt++] = *word_now;
            return *word_now;
        }
        if(file_end){
            token_buf[token_buf_cnt++] = EOF;
            return EOF;
        }
        // �����߽� EOF�� ������İ벿�����Ҷˣ���������һ��
        char * buffer_update = NULL;            // Ҫ���»���������ʼ��ַ
        if(word_now == bufferA_end)
            buffer_update = bufferA_end + 1;
        else
            buffer_update = read_buffer;

        int nums_of_char = fread(buffer_update, 1, BUFFER_LEN / 2, fp_srcfile);

        if(feof(fp_srcfile)){
            *(buffer_update + nums_of_char) = EOF;
            file_end = 1;
        }
        word_now = buffer_update;
        token_buf[token_buf_cnt++] = *word_now;
        return *word_now;
    }
    // ��ջ�����뻺�����ж�ȡ��ʶ��� token
    char * copytoken(){
        token_buf[token_buf_cnt] = '\0';
        //printf("%s ", token_buf);
        return token_buf;
    }
    // �ַ����ˣ��������ַ� ch ѹջ
    void retract(int cnt){
        while(cnt--)
            stack_buf[stack_buf_top++] = token_buf[--token_buf_cnt];
    }
    // �ڷ��ű������в�ѯ��ǰ token,���û������trie���в���
    TokenPairType install_token(char * token, int code_of_kind){
        TrieNode * now = get_from_trie(token);
        now->code_of_kind = (now->code_of_kind == -1) ? code_of_kind : now->code_of_kind;
        return make_pair(now->code_of_kind, (void*)token);
    }
    // ��ʼɨ��һ������
    TokenPairType token_scan(){
        char * token;
        strcpy(token_buf, "");
        token_buf_cnt = 0;

        char ch = getchar_from_buffer();
        if(is_taking_string == 1){              // ʶ���ַ���
            while(ch != '\''){
                string_cnt++;
                if(string_cnt > 20){
                    retract(1); token = copytoken();
                    is_taking_string = 2;
                    error_handle(4, token, ch);
                    return install_token(token, STRING);
                }
                ch = getchar_from_buffer();
            }
            retract(1);
            token = copytoken();
            is_taking_string = 2;
            return install_token(token, STRING);
        }
        while(ch == EOF || ch == ' ' || ch == '\t' || ch == '\n' || ch == '\0'){
            token_buf_cnt--;
            if(ch == '\n') row_cnt++;
            if(ch == EOF) return make_pair(-1, (void*)NULL);
            ch = getchar_from_buffer();
        }
        if(isalpha(ch)){                // ʶ��Ϊ��ʶ����ؼ���
            ch = getchar_from_buffer();
            while(isalnum(ch) || ch == '_') ch = getchar_from_buffer();
            retract(1);
            token = copytoken();
            return install_token(token, ID);
        }
        if(isdigit(ch)){
            ch = getchar_from_buffer();
            while(isdigit(ch)) ch = getchar_from_buffer();
            if(ch == '.'){
                ch = getchar_from_buffer();
                if(ch == '.') {                                  // ʶ��Ϊ����
                    retract(2);
                    token = copytoken();
                    return install_token(token, INT);
                }
                int cnt = 0;
                while(isdigit(ch) || ch == '.'){
                    if(ch == '.') cnt++;
                    ch = getchar_from_buffer();   // ʶ��Ϊʵ��
                }
                retract(1);
                token = copytoken();
                if(cnt > 0) error_handle(1, token, ch);
                return install_token(token, REAL);
            }
            if(isalpha(ch)){
                token = copytoken();
                error_handle(2, token, ch);
            }
            retract(1);
            token = copytoken();
            return install_token(token, INT);   // ʶ��Ϊ����
        }
        switch (ch){
            case '*':
                ch = getchar_from_buffer();
                if(ch == '*') return make_pair(EXP, (void*)NULL);
                retract(1);
                return make_pair(MULTI, (void*)NULL);
                break;
            case ':':
                ch = getchar_from_buffer();
                if(ch == '=') return make_pair(ASSIGN, (void*)NULL);
                retract(1);
                return make_pair(COLON, (void*)NULL);
                break;
            case '<':
                ch = getchar_from_buffer();
                if(ch == '=') return make_pair(LE, (void*)NULL);
                if(ch == '>') return make_pair(NE, (void*)NULL);
                retract(1);
                return make_pair(LT, (void*)NULL);
                break;
            case '=': return make_pair(EQ, (void*)NULL); break;
            case '>':
                ch = getchar_from_buffer();
                if(ch == '=') return make_pair(GE, (void*)NULL);
                retract(1);
                return make_pair(GT, (void*)NULL);
                break;
            case '+': return make_pair(PLUS, (void*)NULL); break;
            case '-': return make_pair(MINUS, (void*)NULL); break;
            case '/':
                ch = getchar_from_buffer();
                if(ch == '/'){                  // ������ע��
                    while(ch != '\n') ch = getchar_from_buffer();
                    return make_pair(-2, (void*)NULL);
                }
                if(ch == '*'){                  // �������ע��
                    ch = getchar_from_buffer();
                    while(ch != '*') ch = getchar_from_buffer();
                    ch = getchar_from_buffer();
                    return make_pair(-2, (void*)NULL);
                }

                retract(1);
                return make_pair(RDIV, (void*)NULL);
                break;
            case ',': return make_pair(COMMA, (void*)NULL); break;
            case ';': return make_pair(SEMIC, (void*)NULL); break;
            case '[': return make_pair(LS_BRAC, (void*)NULL); break;
            case ']': return make_pair(RS_BRAC, (void*)NULL); break;
            case '(': return make_pair(LR_BRAC, (void*)NULL); break;
            case ')': return make_pair(RR_BRAC, (void*)NULL); break;
            case '^': return make_pair(CAP, (void*)NULL); break;
            case '\'':
                is_taking_string = (is_taking_string + 1) % 3;
                if(is_taking_string == 1) string_cnt = 0;
                return make_pair(Q_MARK, (void*)NULL);
                break;
            case '.':
                ch = getchar_from_buffer();
                if(ch == '.') return make_pair(RANGE, (void*)NULL);
                retract(1);
                return make_pair(F_STOP, (void*)NULL);
                break;
            default:
                error_handle(3, "", ch);
                return make_pair(-2, (void*)NULL);
                break;
        }
        return make_pair(-1, (void*) NULL);
    }
    vector<TokenPairType> work(){
        update_keyword_in_trie();
        fp_srcfile = fopen(src_file, "r");
        fp_outfile = fopen(out_file, "w");
        if(fp_srcfile == NULL){
            printf("open file error: %s\n", src_file);
            exit(0);
        }
        if(fp_outfile == NULL){
            printf("open file error: %s\n", out_file);
            exit(0);
        }

        // �Ƚ���뻺��������
        int char_cnt = fread(read_buffer, 1, BUFFER_LEN / 2, fp_srcfile);
        if(char_cnt < BUFFER_LEN / 2) *(read_buffer + char_cnt) = EOF;
        TokenPairType now;
        vector<TokenPairType> word_list;
        word_list.clear();
        while(true){
            now = token_scan();
            if(now.first == -1) break;      // �ʷ��������
            if(now.first == -2) continue;

            word_list.push_back(now);
            if(now.second == NULL){
                fprintf(fp_outfile, "(%d, )\n", now.first);
               // printf("(%d, )\n", now.first);
                continue;
            }
            fprintf(fp_outfile, "(%d, %s)\n", now.first, (char*)now.second);
            //printf("(%d, %s)\n", now.first, (char*)now.second);
        }
        fclose(fp_srcfile);
        fclose(fp_outfile);

        cout << "word_list: "<< word_list.size()<<endl;
        printf("************Lexico Analyze Complete!************\n");
        return word_list;
    }
};

const int MAX_STATE = 2000;         // ״̬��������
const int MAX_T = 500;              // �ս����������
const int MAX_V = 1000;             // ������������
const int V_NUM = 25;
const int T_NUM = 36;
const int ACC   = 0x7fffffff;
const int ERROR = 0;
const char * T_sign[T_NUM] = {
    "prog", "id", "(", ")", "semi", ",", "var", ":", "digits", "..", "of",
    "array", "integer", "real", "[", "]", "begin", "end", "function",
    "procedure", "if", "then", "else", "while", "do", "assignop", "relop",
    "addop", "mulop", "num", "not", "+", "-", "a", "b", "$"
};   // �洢�����ս��
const char * V_sign[V_NUM] = {
    "program", "subprogram_declarations", "identifier_list", "declarations",
    "compound_statement", "declaration", "type", "standard_type",
    "subprogram_declaration", "subprogram_head", "arguments", "parameter_list",
    "optional_statements", "statement_list", "statement", "procedure_statement",
    "variable", "expression", "expression_list", "simple_expression", "term",
    "factor", "sign", "S", "B"
};


int Action[MAX_STATE][MAX_T];   // Si -> i, Rj -> -j, acc = 0x7fffffff, error = 0
int Goto[MAX_STATE][MAX_V];
map<string, int> get_product_num;


class SyntaxAnalyzer{
    stack<pair<int, int> > Stack;   // (״̬���ս��-�� | ����-��)
    vector<string> Production;
    int production_cnt;

public:
    SyntaxAnalyzer(){
        while(!Stack.empty()) Stack.pop();
        Stack.push(make_pair(0, 0));    // ����(S0, '#')
        Production.clear();
        production_cnt = 0;
    }
    void Error_Handle(int i, int error_src){
        printf("Error: No. = %d,  name = %d\n", i, error_src);
    }
    // Ϊ�������(����)���������
    void turn_sign_to_num(){
        sign_to_num["$"] = 0;
        sign_to_num["@"] = 0x3f3f3f3f;  // ��ʾ��ת�Ʒ��� ��
//        sign_to_num["S"] = -2;
//        sign_to_num["B"] = -3;

    }
    // ����ʽ���շ������ж�Ӧ�ı����д
    void make_production(){
        Production.push_back("$");
    }


    // �����ű�
    void make_table(){
        char read_item[1000];
        char production_buf[1000];
        string now_production;

        int len, V_cnt = -1, now_state, next_state;
        memset(Action, 0, sizeof(Action));
        memset(Goto, 0, sizeof(Goto));
//
//        Action[0][sign_to_num["a"]] = 3;
//        Action[0][sign_to_num["b"]] = 4;
//        Action[1][sign_to_num["#"]] = ACC;
//        Action[2][sign_to_num["a"]] = 3;
//        Action[2][sign_to_num["b"]] = 4;
//        Action[3][sign_to_num["a"]] = 3;
//        Action[3][sign_to_num["b"]] = 4;
//        Action[4][sign_to_num["a"]] = -3;
//        Action[4][sign_to_num["b"]] = -3;
//        Action[4][sign_to_num["#"]] = -3;
//        Action[5][sign_to_num["a"]] = -1;
//        Action[5][sign_to_num["b"]] = -1;
//        Action[5][sign_to_num["#"]] = -1;
//        Action[6][sign_to_num["a"]] = -2;
//        Action[6][sign_to_num["b"]] = -2;
//        Action[6][sign_to_num["#"]] = -2;
//
//        Goto[0][-sign_to_num["S"]] = 1;
//        Goto[0][-sign_to_num["B"]] = 2;
//        Goto[2][-sign_to_num["B"]] = 5;
//        Goto[3][-sign_to_num["B"]] = 6;

        fp_srcfile = fopen(LR1_table, "r");

        // ���ȶ����ս���ͱ���
        fscanf(fp_srcfile, "%s", read_item);    // <tr>
        for(int i = 0; i < T_NUM; i++){
            fscanf(fp_srcfile, " <td nowrap>%s", read_item);
            read_item[strlen(read_item) - 5] = '\0';
//            printf("\"%s\", ", read_item);
        }
        // ���������
        for(int i = 0; i < V_NUM; i++){
            fscanf(fp_srcfile, " <td nowrap>%s", read_item);
            read_item[strlen(read_item) - 5] = '\0';
            sign_to_num[string(read_item)] = --V_cnt;
//            printf("\"%s\", ", read_item);
        }
        fscanf(fp_srcfile, "%s", read_item);    // </tr>
        while(!feof(fp_srcfile)){
            fscanf(fp_srcfile, "%s", read_item);    // <tr>
            fscanf(fp_srcfile, " <td nowrap>%d", &now_state);
            fscanf(fp_srcfile, "%s", read_item);    // </td>
            // ���� Action ��
            for(int i = 0; i < T_NUM; i++){
                fscanf(fp_srcfile, " <td nowrap>%s", read_item);
                len = strlen(read_item);
                read_item[len - 5] = '\0';

                if(strcmp(read_item, "&nbsp;") == 0) continue;      // ��
                if(read_item[0] == 'a'){                            // acc
                    Action[now_state][sign_to_num[T_sign[i]]] = ACC;
                }
                if(read_item[0] == 's'){                            // shift
                    next_state = atoi(read_item + 11);
                    Action[now_state][sign_to_num[T_sign[i]]] = next_state;
                }
                if(read_item[0] == 'r'){                            // reduce
                    int k = 12, now_cnt = 0;
                    while(k < len){                                 // ��&nbsp;��Ϊ' '
                        if(read_item[k] != '&')
                            production_buf[now_cnt++] = read_item[k++];
                        else{
                            production_buf[now_cnt++] = ' ';
                            k += 6;
                        }
                    }
                    production_buf[now_cnt] = '\0';
                    // ������ʽ��Ų���������
                    now_production = string(production_buf);
                    if(get_product_num.find(now_production) == get_product_num.end()){
                        Production.push_back(now_production);
                        get_product_num[now_production] = --production_cnt;
                    }
                    Action[now_state][sign_to_num[T_sign[i]]] = get_product_num[now_production];
                }
            }

            // ���� Goto ��
            for(int i = 0; i < V_NUM; i++){
                fscanf(fp_srcfile, " <td nowrap>%s", read_item);
                read_item[strlen(read_item) - 5] = '\0';
                next_state = atoi(read_item);

                Goto[now_state][-sign_to_num[V_sign[i]]] = next_state;
//                printf("%d %s\n", i, read_item);
            }
            fscanf(fp_srcfile, "%s", read_item);    // </tr>
        }
        fclose(fp_srcfile);
    }

    // �����ַ������������һ��Ԫ�ض�Ӧ�ķ��Ŵ�
    int get_next_sign(string & now_product){
        // ����ȥ����β�ո�
        while(now_product[now_product.length() - 1] == ' ')
            now_product.erase(now_product.end() - 1, now_product.end());

        int i, len = now_product.length();
        string now_sign = "";

        if(now_product[len - 1] == '>' && now_product[len - 2] == '-'){
            now_product.erase(now_product.end() - 2, now_product.end());
            return 0;
        }

        for(i = len - 1; i >= 0; i--){
            if(now_product[i] == ' ') break;
            if(now_product[i] == '>' && now_product[i - 1] == '-') break;
            now_sign = now_product[i] + now_sign;
        }
        now_product.erase(now_product.begin() + i + 1, now_product.end());
        return sign_to_num[now_sign];
    }
    // �﷨��������
    void work(vector<TokenPairType> word_buf){
        int state, op, now_sign, now_T;
        string now_product;
        word_buf.push_back(make_pair(0, (void*)NULL));     // �������к���� '#'

        turn_sign_to_num();
        make_production();
        make_table();

        for(unsigned int i = 0; i < word_buf.size(); i++){
            state = Stack.top().first;
            now_T = word_buf[i].first;
            op = Action[state][now_T];
            //printf("%d  %d   op = %d\n", state, now_T, op);
            if(op == ACC){
                Stack.pop();        // ��ʱջ�ָ�����ʼ״̬��������һ������ʹ��
                //printf("Complete sentence number: %d\n", ++sentence_cnt);
                continue;
            }
            if(op == ERROR){
                Error_Handle(i, now_T);
                return;
            }
            // �ƽ�����
            if(op > 0){
                Stack.push(make_pair(op, now_T));
                continue;
            }
            // ��Լ����
            now_product = Production[-op];
            cout << now_product << endl;
            while(true){
                now_sign = get_next_sign(now_product);
                if(now_sign == 0){
                    now_sign = -get_next_sign(now_product);
                    state = Stack.top().first;
                    // ����Goto��ת��״̬
                    Stack.push(make_pair(Goto[state][now_sign], -now_sign));
                    i--;        // ��ʱ�����ƽ��ս��
                    break;
                }
                if(now_sign == sign_to_num["@"]) continue;  // ��ת��
                if(Stack.top().second == now_sign)
                    Stack.pop();
                else
                    Error_Handle(i, now_sign);
            }
        }
        printf("************Syntax Analyze Complete!************\n");
    }
};

int main()
{
    LexicoAnalyzer A;
    SyntaxAnalyzer B;

    vector<TokenPairType> word_list = A.work();

    B.work(word_list);
//    B.make_table();
    return 0;
}
