#include <iostream>
#include <cstdio>
#include <stdlib.h>
#include <string.h>
#include <vector>
#include <stack>
#include <map>
#include <queue>
#define MP make_pair

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
const char * src_file = "qsort.pas";                // �����ļ�·��
const char * out_file = "word_stream.txt";         // ����ļ�·��
const char * LR1_table = "LR1_table1.htm";         // LR1������
FILE *fp_srcfile = NULL;                        // �����ļ�ָ��
FILE *fp_outfile = NULL;                        // ����ļ�ָ��

vector<TokenPairType> word_list;

struct SignTableType{
    string name;
    string type;
    int width;
    int offset;         // �ڹ����������е���Ե�ַ
    void * toVal;       // ָ����̵ķ��ű��ַ
    SignTableType(){
        name = type = "";
        width = offset = 0;
        toVal = (void*) NULL;
    }
};
struct NestSignTable{
    SignTableType SignTable[100];           // �洢������ű���Ŀ
    int sign_table_cnt;                     // �ѷ�����Ŀ
    map<string, int> get_SignTable_pos;     // �˷��ű�Ĺ�ϣ����
    NestSignTable *lastTable;               // ָ����һ����ű�
    int offset;                             // ��ǰ����ƫ����
    string name;                            // ��ǰ�Ӻ���������
    string type;                            // ��ǰ�Ӻ���������
    string ret_val;                         // ��ǰ�Ӻ����ķ�������
    NestSignTable(){
        get_SignTable_pos.clear();
        sign_table_cnt = offset = 0;
        lastTable = NULL; name = type = ret_val = "";
    }
};
pair<NestSignTable*, int> stack_sign_table[10];     // �洢���ű��ε�ջ
int table_top = 0;                             // ջ��
NestSignTable* nowSignTable = NULL;                     // ��ǰ���ű�ָ��
int temp_var_cnt = 0;                           // �˿�ʹ�õ���ʱ�����ĸ���
int row_cnt = 0;                                // ͳ���м���������



// ���Խڵ㶨��
struct AttrNodeType{
    string name;
    string type;
    string value;
    int width;
    AttrNodeType(){
        name = type = value = "";
        width = 0;
    }
}Stack_attr[1000];    // ����ջ
int attr_top = 0;   // ջ��


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
        //install_keyword("relop", RELOP);    install_keyword("addop", PLUS);
        //install_keyword("mulop", MULTI);
        install_keyword("num", INT);

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
    void work(){
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
            // ��Ҫ������һ���ڴ棬�������е�word_list.second��ָ����ͬһ����ַ
            word_list[word_list.size() - 1].second = malloc(strlen((char*)now.second) + 1);
            memcpy(word_list[word_list.size() - 1].second, (char*)now.second, strlen((char*)now.second) + 1);
            fprintf(fp_outfile, "(%d, %s)\n", now.first, (char*)now.second);
            //printf("(%d, %s)\n", now.first, (char*)now.second);
        }
        fclose(fp_srcfile);
        fclose(fp_outfile);

        cout << "word_list: "<< word_list.size()<<endl;
        printf("************Lexico Analyze Complete!************\n\n");
        return;
    }
};

const int MAX_STATE = 2000;         // ״̬��������
const int MAX_T = 500;              // �ս����������
const int MAX_V = 1000;             // ������������
const int V_NUM = 29;
const int T_NUM = 46;
const int ACC   = 0x7fffffff;
const int ERROR = 0;

char * T_sign[T_NUM];               // LR1���е��ս��
char * V_sign[V_NUM];               // LR1���еı���
// �� �շ���

int Action[MAX_STATE][MAX_T];   // Si -> i, Rj -> -j, acc = 0x7fffffff, error = 0
int Goto[MAX_STATE][MAX_V];
map<string, int> get_product_num;


class SyntaxAnalyzer{
    stack<pair<int, int> > Stack;   // (״̬���ս��-�� | ����-��)
    stack<pair<int, void*> > Stack_word;        // �洢�ʷ�������Ӧ���ս��������

    vector<string> Production;
    int production_cnt;
    vector<AttrNodeType> attr_node_list;     // �������ʱ�����Խڵ����

public:
    SyntaxAnalyzer(){
        while(!Stack.empty()) Stack.pop();
        while(!Stack_word.empty()) Stack_word.pop();
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

    }
    // ����ʽ���շ������ж�Ӧ�ı����д
    void make_production(){
        Production.push_back("$");
    }

    // ���Action �� Goto���ű�
    void make_table(){
        char read_item[1000];
        char production_buf[1000];
        string now_production;

        int len, V_cnt = -1, now_state, next_state;
        memset(Action, 0, sizeof(Action));
        memset(Goto, 0, sizeof(Goto));

        fp_srcfile = fopen(LR1_table, "r");
        if(fp_srcfile == NULL){
            printf("open file error: %s\n", src_file);
            exit(0);
        }

        // ���ȶ����ս���ͱ���
        fscanf(fp_srcfile, "%s", read_item);    // <tr>
        for(int i = 0; i < T_NUM; i++){
            fscanf(fp_srcfile, " <td nowrap>%s", read_item);
            read_item[strlen(read_item) - 5] = '\0';
            T_sign[i] = (char *)malloc(strlen(read_item + 6));
            strcpy(T_sign[i], read_item);
//            printf("\"%s\", ", read_item);
        }
        // ���������
        for(int i = 0; i < V_NUM; i++){
            fscanf(fp_srcfile, " <td nowrap>%s", read_item);
            read_item[strlen(read_item) - 5] = '\0';
            V_sign[i] = (char *)malloc(strlen(read_item + 6));
            strcpy(V_sign[i], read_item);
            sign_to_num[string(read_item)] = --V_cnt;   // �����ı���Ǹ���
//            printf("\"%s\", ", read_item);
        }
        fscanf(fp_srcfile, "%s", read_item);    // </tr>
        while(true){
            fscanf(fp_srcfile, "%s", read_item);    // <tr>
            //printf("%s\n", read_item);
            if(strcmp(read_item, "</table>") == 0) break;
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
                        get_product_num[now_production] = --production_cnt; // ����ʽ���Ϊ����
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
            return 0;   // ��Լʽ�еļ�ͷ
        }

        for(i = len - 1; i >= 0; i--){
            if(now_product[i] == ' ') break;
            if(now_product[i] == '>' && now_product[i - 1] == '-') break;
            now_sign = now_product[i] + now_sign;
        }
        now_product.erase(now_product.begin() + i + 1, now_product.end());
        return sign_to_num[now_sign];
    }

    // �����ű�
    void enterTable(NestSignTable * nowTable, string name, string type, int width, void *toVal){
        // ��ϣһ�£��õ����ڷ��ű��е��±�
        if(nowTable->get_SignTable_pos.find(name) == nowTable->get_SignTable_pos.end())
            nowTable->get_SignTable_pos[name] = ++nowTable->sign_table_cnt;
        // �����������ֺ�����������ű���
        int now_index = nowTable->get_SignTable_pos[name];
        nowTable->SignTable[now_index].name = name;
        nowTable->SignTable[now_index].type = type;
        nowTable->SignTable[now_index].width = width;
        nowTable->SignTable[now_index].offset = nowTable->offset;
        nowTable->SignTable[now_index].toVal = toVal;
        nowTable->offset += width;
        //cout << n2ame << " " << type << " " << nowTable->sign_table_cnt << endl;
    }


    // ����һ���µķ��ű�
    NestSignTable *mktable(NestSignTable * nowTable){
        NestSignTable *newTable = new NestSignTable;
        newTable->lastTable = nowTable;                     // ָ����һ����ű�
        stack_sign_table[++table_top] = MP(newTable, 0);    // ���·��ű�ջ
        return newTable;
    }

    // �����ű����ҵ���Ϊ name ��λ��
    int lookup(string name){
        if(nowSignTable->get_SignTable_pos.find(name) == nowSignTable->get_SignTable_pos.end())
            return -1;  // ���ű���û�ҵ������ش���
        return nowSignTable->get_SignTable_pos[name];
    }
    // ʹ���µ���ʱ��������ͨ������ƥ�������ظ�ʹ����ʱ����
    AttrNodeType newtemp(){
        char temp[10];
        sprintf(temp, "%d", temp_var_cnt++);
        string tempName = "$" + string(temp);
        // ������ڷ��ű������ڷ��ű�������һ��λ��
        if(nowSignTable->get_SignTable_pos.find(tempName) == nowSignTable->get_SignTable_pos.end())
            enterTable(nowSignTable, tempName, "TempVar", 4, (void*)NULL);
        int now_index = nowSignTable->get_SignTable_pos[tempName];
        AttrNodeType nowTemp;
        nowTemp.name = nowSignTable->SignTable[now_index].name;
        nowTemp.type = nowSignTable->SignTable[now_index].type;
        nowTemp.width = 4;
        return nowTemp;
    }

    // �����м����
    void gencode(AttrNodeType *ans, AttrNodeType *A, AttrNodeType *op, AttrNodeType *B){
        printf("%d:\t", ++row_cnt);
        if(A == NULL && op == NULL){
            cout << ans->name << " := " << B->name  << endl;
            return;
        }
        cout << ans->name << " := " << A->name << " " << op->name << " " << B->name << endl;
    }


    // ���ݲ���ʽ�����������
    void SemanticAnalysis(string Production, AttrNodeType & ansAttr)
    {
        ansAttr.name = ansAttr.type = ansAttr.value = "";
        ansAttr.width = 0;
        // ��������б�
        if(Production == "identifier_list -> id"){
            attr_node_list.clear();         // ������������
            attr_node_list.push_back(Stack_attr[attr_top]);
            return;
        }
        if(Production == "identifier_list -> identifier_list , id"){
            attr_node_list.push_back(Stack_attr[attr_top]);       // ���β����һ��
            return;
        }

        // �������
        if(Production == "declarations -> var declaration semi"){
            return;
        }
        if(Production == "declaration -> declaration semi identifier_list : type"){
            // �������е����Խڵ����������Ӧ�ķ��ű���
            for(unsigned int i = 0; i < attr_node_list.size(); i++)
                enterTable(nowSignTable, attr_node_list[i].name, Stack_attr[attr_top].type,
                            Stack_attr[attr_top].width, (void*)NULL);
            return;
        }
        if(Production == "declaration -> identifier_list : type"){
            // �������е����Խڵ����������Ӧ�ķ��ű���
            for(unsigned int i = 0; i < attr_node_list.size(); i++)
                enterTable(nowSignTable, attr_node_list[i].name, Stack_attr[attr_top].type,
                            Stack_attr[attr_top].width, (void*)NULL);
            return;
        }
        if(Production == "type -> standard_type"){
            ansAttr.type = Stack_attr[attr_top].type;
            ansAttr.width = Stack_attr[attr_top].width;
            return;
        }
        if(Production == "type -> array [ digits .. digits ] of standard_type"){
            // �������ͣ�ʹ�����ͱ��ʽ
            int low_index = atoi(Stack_attr[attr_top - 5].value.c_str());
            int high_index = atoi(Stack_attr[attr_top - 3].value.c_str());
            int num = high_index - low_index + 1;
            char strNum[100];
            sprintf(strNum, "%d", num);

            ansAttr.type = "array(" +  string(strNum) + "," + Stack_attr[attr_top].type + ")";
            ansAttr.width = num * Stack_attr[attr_top].width;
            return;
        }

        if(Production == "standard_type -> integer"){
            ansAttr.type = "integer";
            ansAttr.width = 4;
            return;
        }
        if(Production == "standard_type -> real"){
            ansAttr.type = "real";
            ansAttr.width = 8;
            return;
        }

        // ���̺ͺ��������Ͷ���ķ���
        if(Production == "subprogram_declarations -> @"){
            // �����·��ű�������ǰ���ű����Ϊ���·��ű�ͬʱ�����˷��ű�ջ
            nowSignTable = mktable(nowSignTable);
            return;
        }
        if(Production == "parameter_list -> identifier_list : type"){
            // ��������ʱ�Ĳ����б�
            // �������е����Խڵ����������Ӧ�ķ��ű���
            for(unsigned int i = 0; i < attr_node_list.size(); i++)
                enterTable(nowSignTable, attr_node_list[i].name, Stack_attr[attr_top].type,
                            Stack_attr[attr_top].width, (void*)NULL);
            return;
        }
        if(Production == "subprogram_head -> procedure id arguments semi"){
            // ��ǰ����������䣬��¼������
            nowSignTable->name = Stack_attr[attr_top - 2].name;
            nowSignTable->type = "procedure";
            return;
        }
        if(Production == "subprogram_head -> function id arguments : standard_type semi"){
            // ��ǰ����������䣬��¼������
            nowSignTable->name = Stack_attr[attr_top - 4].name;
            nowSignTable->type = "function";
            nowSignTable->ret_val = Stack_attr[attr_top - 1].type;
            return;
        }
        if(Production == "subprogram_declaration -> subprogram_head declarations compound_statement"){
            // �ӹ��̴�����ϣ����ű�Ӧ�˻�Ϊ��һ��,���� ��һ����ű��б�Ǵ˷��ű��ַ
            NestSignTable *lastTable = nowSignTable->lastTable;
            enterTable(lastTable, nowSignTable->name, nowSignTable->type,
                       4, (void*)nowSignTable);
            table_top--;        // ���ű�ջ��һ��
            nowSignTable = lastTable;       // ָ����һ��ķ��ű�
            return;
        }

        // ���̺ͺ������õķ���



        // ���ʽ���㼰��ֵ��䷭��
        // �Ƚ��з��ŷ���
        if(Production == "assignop -> :="){
            ansAttr.name = ansAttr.type = ":=";
            return;
        }
        if(Production == "addop -> +" || Production == "addop -> -"
           || Production == "addop -> or"){
            ansAttr.name = ansAttr.type = Production[Production.length() - 1];
            if (Production == "addop -> or")
                ansAttr.name = ansAttr.type = "or";
            return;
        }
        if(Production == "mulop -> *" || Production == "mulop -> /"){
            ansAttr.name = ansAttr.type = Production[Production.length() - 1];
            return;
        }
        if(Production == "mulop -> div" || Production == "mulop -> mod"
           || Production == "mulop -> and"){
            ansAttr.name = ansAttr.type = Production.substr(Production.length() - 3, 3);
            return;
        }
        if(Production == "sign -> +" || Production == "sign -> -"){
            ansAttr.name = ansAttr.type = Production[Production.length() - 1];
            return;
        }
        // ���ʽ����
        if(Production == "variable -> id" || Production == "factor -> id"
           || Production == "term -> factor" || Production == "simple_expression -> term"
           || Production == "expression -> simple_expression"){
            // ��ֵ�����ֵ
            int pos = lookup(Stack_attr[attr_top].name);
            // �����Ǳ�ʶ���ű�����Ϊ���������ķ��������ʽҲ�����õ���Щ����ʽ
            if(pos < 0 && Stack_attr[attr_top].type == "ID"){
                printf("Error:-----Can't find name in SignTable(%s): %s\n",
                        nowSignTable->name.c_str(), Stack_attr[attr_top].name.c_str());
                return;
            }

            ansAttr = Stack_attr[attr_top]; // �� id �����Ը�variable
            return;
        }
        if(Production == "term -> term mulop factor" ||
           Production == "simple_expression -> simple_expression addop term"){
            // ��������ƥ�����ʼ�����ʱ����������
            if(Stack_attr[attr_top - 2].type == "TempVar") temp_var_cnt--;
            if(Stack_attr[attr_top].type == "TempVar") temp_var_cnt--;
            ansAttr = newtemp();            // ʹ����ʱ����
            gencode(&ansAttr, &Stack_attr[attr_top - 2], &Stack_attr[attr_top - 1],
                    &Stack_attr[attr_top]);
            return;
        }
        if(Production == "statement -> variable assignop expression"){
            // ��������ƥ�����ʼ�����ʱ����������
            int pos = lookup(Stack_attr[attr_top - 2].name);
            if(pos < 0 && Stack_attr[attr_top].type == "ID"){
                printf("Error:-----Can't find name in SignTable(%s): %s\n",
                        nowSignTable->name.c_str(), Stack_attr[attr_top].name.c_str());
                return;
            }

            gencode(&Stack_attr[attr_top - 2], NULL, NULL, &Stack_attr[attr_top]);
            return;
        }





    }

    // ��ȡ�ս��������ֵ
    void get_attr_from_T(AttrNodeType & T_Node, int now_T, void *now_T_data)
    {
        string temp = "";
        if(now_T_data != NULL){
            temp= string((char*)now_T_data);
        }
        if(now_T == ID){
            T_Node.name = temp;
            T_Node.type = "ID";
        }
        T_Node.value = temp;
    }


    // �﷨��������
    void work(vector<TokenPairType> & word_buf){
        int state, op, now_sign, now_T;
        void *now_T_data;
        vector<pair<int, void*> > now_T_list;   // �洢�����������ս���������ݵ�����
        string now_product;
        word_buf.push_back(make_pair(0, (void*)NULL));     // �������к���� '#'
        attr_top = 0;           // ����ջ���
        // �����ܵķ��ű�, ������ջ��
        nowSignTable = new NestSignTable;
        stack_sign_table[++table_top] = MP(nowSignTable, 0);

        turn_sign_to_num();
        make_production();
        make_table();

        now_T_list.clear();
        for(unsigned int i = 0; i < word_buf.size(); i++){

            state = Stack.top().first;
            now_T = word_buf[i].first;
            now_T_data = word_buf[i].second;
            //printf("(%d, %s) ", now_T, word_buf[i].second);
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
                Stack_word.push(word_buf[i]);
                // ��������ջ������ȡ������
                ++attr_top;

                get_attr_from_T(Stack_attr[attr_top], now_T, now_T_data);
                continue;
            }
            // ��Լ����
            now_product = Production[-op];
            //cout << now_product << endl;    // ���������ʽȥ��Լ

            string temp_product = now_product;      // �ݴ����ʽ


            AttrNodeType ansAttr;               // �洢�����������ڵ�
            SemanticAnalysis(temp_product, ansAttr);  // �����������

            while(true){
                now_sign = get_next_sign(now_product);
                if(now_sign == 0){
                    now_sign = -get_next_sign(now_product); // ��Լ���ı���
                    state = Stack.top().first;
                    // ����Goto��ת��״̬
                    Stack.push(make_pair(Goto[state][now_sign], -now_sign));
                    Stack_word.push(make_pair(0, (void*)NULL));    // Ϊ��Stack����һ�£�����һ���ն�
                    Stack_attr[++attr_top] = ansAttr;           // �������Է��������ջ
                    i--;        // ��ʱ�����ƽ��ս��

                    // ����������
//                    cout << temp_product << "   ";
//                    for(unsigned int i = 0; i < now_T_list.size(); i++)
//                        printf("(%d,%s) ", now_T_list[i].first, (char*)now_T_list[i].second);
//                    cout << endl;
                    now_T_list.clear(); // ���β���ʽ������ϣ������ʱ����
//                    cout << endl;
                    break;
                }
                if(now_sign == sign_to_num["@"]) continue;  // ��ת��
                if(Stack.top().second == now_sign){     // ȡ����ʱ���ս��
                    if(Stack.top().second > 0)
                        now_T_list.push_back(Stack_word.top());     // �洢�����˲���ʽʱ���ս������
                    Stack_word.pop();
                    Stack.pop();
                    attr_top--;         //  ��������ջ��ջ
                }
                else
                    Error_Handle(i, now_sign);
            }
        }
        cout << Production.size() << endl;
        printf("************Syntax Analyze Complete!************\n\n");
    }
};

// ��ӡ���з��ű������
void print_SignTable(){
    queue<NestSignTable *> Q;
    while(!Q.empty()) Q.pop();
    Q.push(nowSignTable);
    while(!Q.empty()){
        NestSignTable * now = Q.front(); Q.pop();
        printf("-------------TableName:%s -----------------\n", now->name.c_str());
        for(int i = 1; i <= now->sign_table_cnt; i++){
            printf("name = %s\t width = %d\t type = %s\t offset = %d\n",
                   now->SignTable[i].name.c_str(),
                   now->SignTable[i].width,
                   now->SignTable[i].type.c_str(),
                   now->SignTable[i].offset);
            if(now->SignTable[i].type == "function" ||
               now->SignTable[i].type == "procedure"){
                Q.push((NestSignTable*) now->SignTable[i].toVal);
            }
        }
    }


}

int main()
{
    LexicoAnalyzer A;
    SyntaxAnalyzer B;

    A.work();
    B.work(word_list);

    print_SignTable();


    return 0;
}
