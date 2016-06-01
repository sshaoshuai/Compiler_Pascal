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

// 字典树节点结构定义
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

map<string, int> sign_to_num;   // 将终结符和变量转化为数字  终结符-正 | 变量-负

const int BUFFER_LEN = 100;                     // 输入缓存区大小
const char * src_file = "qsort.pas";                // 输入文件路径
const char * out_file = "word_stream.txt";         // 输出文件路径
const char * LR1_table = "LR1_table1.htm";         // LR1分析表
FILE *fp_srcfile = NULL;                        // 输入文件指针
FILE *fp_outfile = NULL;                        // 输出文件指针

vector<TokenPairType> word_list;

struct SignTableType{
    string name;
    string type;
    int width;
    int offset;         // 在过程数据区中的相对地址
    void * toVal;       // 指向过程的符号表地址
    SignTableType(){
        name = type = "";
        width = offset = 0;
        toVal = (void*) NULL;
    }
};
struct NestSignTable{
    SignTableType SignTable[100];           // 存储具体符号表条目
    int sign_table_cnt;                     // 已分配条目
    map<string, int> get_SignTable_pos;     // 此符号表的哈希索引
    NestSignTable *lastTable;               // 指向上一层符号表
    int offset;                             // 当前数据偏移量
    string name;                            // 当前子函数的名称
    string type;                            // 当前子函数的类型
    string ret_val;                         // 当前子函数的返回类型
    NestSignTable(){
        get_SignTable_pos.clear();
        sign_table_cnt = offset = 0;
        lastTable = NULL; name = type = ret_val = "";
    }
};
pair<NestSignTable*, int> stack_sign_table[10];     // 存储符号表层次的栈
int table_top = 0;                             // 栈顶
NestSignTable* nowSignTable = NULL;                     // 当前符号表指针
int temp_var_cnt = 0;                           // 此刻使用的临时变量的个数
int row_cnt = 0;                                // 统计中间代码的行数



// 属性节点定义
struct AttrNodeType{
    string name;
    string type;
    string value;
    int width;
    AttrNodeType(){
        name = type = value = "";
        width = 0;
    }
}Stack_attr[1000];    // 属性栈
int attr_top = 0;   // 栈顶


// 词法分析器类
class LexicoAnalyzer{
    char *src_data;                    // 源程序指针
    char *read_buffer;                 // 输入缓存区，采用带标记的双缓存区实现
    char *word_now;                    // 读入词汇时当前指针
    char *bufferA_end, *bufferB_end;   // 两个缓存区的右边界指针
    char stack_buf[BUFFER_LEN];        // 模拟回退缓存栈
    char token_buf[BUFFER_LEN];        // 识别 token 时暂存区
    int  file_len, stack_buf_top, token_buf_cnt;
    int  is_taking_string, row_cnt, file_end, string_cnt;
public:
    // 构造函数，用于词法分析器的初始化
    LexicoAnalyzer(){
        // 带标记的双缓存区的初始化, 0-49, EOF(50), 51-100, EOF
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
    // 读取整个文件，测试用
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
    //根据当前字符获取在 trie 树中 next 下标
    int get_trie_index(char ch){
        if(ch >= 'A' && ch <= 'Z')
            return ch - 'A' + 'a';
        return ch;
    }

    // 从 Trie 树中获取当前结点，如果没有就插入节点，返回这个节点的指针
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
    // 将当前关键字插入到 Trie 树中
    void install_keyword(const char * keyword, int code_of_kind){
        TrieNode * now = get_from_trie(keyword);
        now->code_of_kind = code_of_kind;

        sign_to_num[string(keyword)] = code_of_kind;    // 将终结符映射添加到转化表中
    }
    // 预处理，将所有keyword插入到 Trie 树中
    void update_keyword_in_trie(){
        sign_to_num.clear();
        // 测试用例
        install_keyword("id", ID);          install_keyword("semi", SEMIC);
        install_keyword("digits", INT);     install_keyword("integer", INTEGER);
        install_keyword("real", REALTYPE);  install_keyword("assignop", ASSIGN);
        //install_keyword("relop", RELOP);    install_keyword("addop", PLUS);
        //install_keyword("mulop", MULTI);
        install_keyword("num", INT);

        // 保留字
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
        // 符号
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
    // 从缓存区读取字符，兼顾双缓存区的维护
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
        // 碰到边界 EOF， 检测是哪半部分最右端，并更新另一半
        char * buffer_update = NULL;            // 要更新缓存区的起始地址
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
    // 从栈及输入缓存区中读取已识别的 token
    char * copytoken(){
        token_buf[token_buf_cnt] = '\0';
        //printf("%s ", token_buf);
        return token_buf;
    }
    // 字符回退，将回退字符 ch 压栈
    void retract(int cnt){
        while(cnt--)
            stack_buf[stack_buf_top++] = token_buf[--token_buf_cnt];
    }
    // 在符号表索引中查询当前 token,如果没有则在trie树中插入
    TokenPairType install_token(char * token, int code_of_kind){
        TrieNode * now = get_from_trie(token);
        now->code_of_kind = (now->code_of_kind == -1) ? code_of_kind : now->code_of_kind;

        return make_pair(now->code_of_kind, (void*)token);
    }
    // 开始扫描一个单词
    TokenPairType token_scan(){
        char * token;
        strcpy(token_buf, "");
        token_buf_cnt = 0;

        char ch = getchar_from_buffer();
        if(is_taking_string == 1){              // 识别字符串
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
        if(isalpha(ch)){                // 识别为标识符或关键字
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
                if(ch == '.') {                                  // 识别为整数
                    retract(2);
                    token = copytoken();
                    return install_token(token, INT);
                }
                int cnt = 0;
                while(isdigit(ch) || ch == '.'){
                    if(ch == '.') cnt++;
                    ch = getchar_from_buffer();   // 识别为实数
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
            return install_token(token, INT);   // 识别为整数
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
                if(ch == '/'){                  // 处理单行注释
                    while(ch != '\n') ch = getchar_from_buffer();
                    return make_pair(-2, (void*)NULL);
                }
                if(ch == '*'){                  // 处理多行注释
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

        // 先将左半缓存区读满
        int char_cnt = fread(read_buffer, 1, BUFFER_LEN / 2, fp_srcfile);
        if(char_cnt < BUFFER_LEN / 2) *(read_buffer + char_cnt) = EOF;
        TokenPairType now;
        word_list.clear();
        while(true){
            now = token_scan();
            if(now.first == -1) break;      // 词法分析完成
            if(now.first == -2) continue;

            word_list.push_back(now);
            if(now.second == NULL){
                fprintf(fp_outfile, "(%d, )\n", now.first);
               // printf("(%d, )\n", now.first);
                continue;
            }
            // 需要新申请一块内存，否则所有的word_list.second都指向了同一个地址
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

const int MAX_STATE = 2000;         // 状态数的上限
const int MAX_T = 500;              // 终结符数的上限
const int MAX_V = 1000;             // 变量数的上限
const int V_NUM = 29;
const int T_NUM = 46;
const int ACC   = 0x7fffffff;
const int ERROR = 0;

char * T_sign[T_NUM];               // LR1表中的终结符
char * V_sign[V_NUM];               // LR1表中的变量
// ε 空符号

int Action[MAX_STATE][MAX_T];   // Si -> i, Rj -> -j, acc = 0x7fffffff, error = 0
int Goto[MAX_STATE][MAX_V];
map<string, int> get_product_num;


class SyntaxAnalyzer{
    stack<pair<int, int> > Stack;   // (状态，终结符-正 | 变量-负)
    stack<pair<int, void*> > Stack_word;        // 存储词法分析对应的终结符数据域

    vector<string> Production;
    int production_cnt;
    vector<AttrNodeType> attr_node_list;     // 语义分析时的属性节点队列

public:
    SyntaxAnalyzer(){
        while(!Stack.empty()) Stack.pop();
        while(!Stack_word.empty()) Stack_word.pop();
        Stack.push(make_pair(0, 0));    // 代表(S0, '#')
        Production.clear();
        production_cnt = 0;
    }
    void Error_Handle(int i, int error_src){
        printf("Error: No. = %d,  name = %d\n", i, error_src);
    }
    // 为变量编号(负数)，方便分析
    void turn_sign_to_num(){
        sign_to_num["$"] = 0;
        sign_to_num["@"] = 0x3f3f3f3f;  // 表示空转移符号 ε

    }
    // 产生式按照分析表中对应的编号填写
    void make_production(){
        Production.push_back("$");
    }

    // 填充Action 和 Goto符号表
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

        // 首先读入终结符和变量
        fscanf(fp_srcfile, "%s", read_item);    // <tr>
        for(int i = 0; i < T_NUM; i++){
            fscanf(fp_srcfile, " <td nowrap>%s", read_item);
            read_item[strlen(read_item) - 5] = '\0';
            T_sign[i] = (char *)malloc(strlen(read_item + 6));
            strcpy(T_sign[i], read_item);
//            printf("\"%s\", ", read_item);
        }
        // 给变量编号
        for(int i = 0; i < V_NUM; i++){
            fscanf(fp_srcfile, " <td nowrap>%s", read_item);
            read_item[strlen(read_item) - 5] = '\0';
            V_sign[i] = (char *)malloc(strlen(read_item + 6));
            strcpy(V_sign[i], read_item);
            sign_to_num[string(read_item)] = --V_cnt;   // 变量的编号是负的
//            printf("\"%s\", ", read_item);
        }
        fscanf(fp_srcfile, "%s", read_item);    // </tr>
        while(true){
            fscanf(fp_srcfile, "%s", read_item);    // <tr>
            //printf("%s\n", read_item);
            if(strcmp(read_item, "</table>") == 0) break;
            fscanf(fp_srcfile, " <td nowrap>%d", &now_state);
            fscanf(fp_srcfile, "%s", read_item);    // </td>
            // 生成 Action 表
            for(int i = 0; i < T_NUM; i++){
                fscanf(fp_srcfile, " <td nowrap>%s", read_item);
                len = strlen(read_item);
                read_item[len - 5] = '\0';

                if(strcmp(read_item, "&nbsp;") == 0) continue;      // 空
                if(read_item[0] == 'a'){                            // acc
                    Action[now_state][sign_to_num[T_sign[i]]] = ACC;
                }
                if(read_item[0] == 's'){                            // shift
                    next_state = atoi(read_item + 11);
                    Action[now_state][sign_to_num[T_sign[i]]] = next_state;
                }
                if(read_item[0] == 'r'){                            // reduce
                    int k = 12, now_cnt = 0;
                    while(k < len){                                 // 将&nbsp;变为' '
                        if(read_item[k] != '&')
                            production_buf[now_cnt++] = read_item[k++];
                        else{
                            production_buf[now_cnt++] = ' ';
                            k += 6;
                        }
                    }
                    production_buf[now_cnt] = '\0';
                    // 给产生式编号并填充分析表
                    now_production = string(production_buf);
                    if(get_product_num.find(now_production) == get_product_num.end()){
                        Production.push_back(now_production);
                        get_product_num[now_production] = --production_cnt; // 产生式编号为负数
                    }
                    Action[now_state][sign_to_num[T_sign[i]]] = get_product_num[now_production];
                }
            }

            // 生成 Goto 表
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

    // 解析字符串，返回最后一个元素对应的符号串
    int get_next_sign(string & now_product){
        // 首先去除句尾空格
        while(now_product[now_product.length() - 1] == ' ')
            now_product.erase(now_product.end() - 1, now_product.end());

        int i, len = now_product.length();
        string now_sign = "";

        if(now_product[len - 1] == '>' && now_product[len - 2] == '-'){
            now_product.erase(now_product.end() - 2, now_product.end());
            return 0;   // 归约式中的箭头
        }

        for(i = len - 1; i >= 0; i--){
            if(now_product[i] == ' ') break;
            if(now_product[i] == '>' && now_product[i - 1] == '-') break;
            now_sign = now_product[i] + now_sign;
        }
        now_product.erase(now_product.begin() + i + 1, now_product.end());
        return sign_to_num[now_sign];
    }

    // 填充符号表
    void enterTable(NestSignTable * nowTable, string name, string type, int width, void *toVal){
        // 哈希一下，得到其在符号表中的下标
        if(nowTable->get_SignTable_pos.find(name) == nowTable->get_SignTable_pos.end())
            nowTable->get_SignTable_pos[name] = ++nowTable->sign_table_cnt;
        // 将变量的名字和类型填入符号表中
        int now_index = nowTable->get_SignTable_pos[name];
        nowTable->SignTable[now_index].name = name;
        nowTable->SignTable[now_index].type = type;
        nowTable->SignTable[now_index].width = width;
        nowTable->SignTable[now_index].offset = nowTable->offset;
        nowTable->SignTable[now_index].toVal = toVal;
        nowTable->offset += width;
        //cout << n2ame << " " << type << " " << nowTable->sign_table_cnt << endl;
    }


    // 创建一个新的符号表
    NestSignTable *mktable(NestSignTable * nowTable){
        NestSignTable *newTable = new NestSignTable;
        newTable->lastTable = nowTable;                     // 指向上一层符号表
        stack_sign_table[++table_top] = MP(newTable, 0);    // 更新符号表栈
        return newTable;
    }

    // 到符号表中找到名为 name 的位置
    int lookup(string name){
        if(nowSignTable->get_SignTable_pos.find(name) == nowSignTable->get_SignTable_pos.end())
            return -1;  // 符号表中没找到，返回错误
        return nowSignTable->get_SignTable_pos[name];
    }
    // 使用新的临时变量，并通过括号匹配性质重复使用临时变量
    AttrNodeType newtemp(){
        char temp[10];
        sprintf(temp, "%d", temp_var_cnt++);
        string tempName = "$" + string(temp);
        // 如果不在符号表中则在符号表中申请一个位置
        if(nowSignTable->get_SignTable_pos.find(tempName) == nowSignTable->get_SignTable_pos.end())
            enterTable(nowSignTable, tempName, "TempVar", 4, (void*)NULL);
        int now_index = nowSignTable->get_SignTable_pos[tempName];
        AttrNodeType nowTemp;
        nowTemp.name = nowSignTable->SignTable[now_index].name;
        nowTemp.type = nowSignTable->SignTable[now_index].type;
        nowTemp.width = 4;
        return nowTemp;
    }

    // 生成中间代码
    void gencode(AttrNodeType *ans, AttrNodeType *A, AttrNodeType *op, AttrNodeType *B){
        printf("%d:\t", ++row_cnt);
        if(A == NULL && op == NULL){
            cout << ans->name << " := " << B->name  << endl;
            return;
        }
        cout << ans->name << " := " << A->name << " " << op->name << " " << B->name << endl;
    }


    // 根据产生式进行语义分析
    void SemanticAnalysis(string Production, AttrNodeType & ansAttr)
    {
        ansAttr.name = ansAttr.type = ansAttr.value = "";
        ansAttr.width = 0;
        // 处理参数列表
        if(Production == "identifier_list -> id"){
            attr_node_list.clear();         // 待处理队列清空
            attr_node_list.push_back(Stack_attr[attr_top]);
            return;
        }
        if(Production == "identifier_list -> identifier_list , id"){
            attr_node_list.push_back(Stack_attr[attr_top]);       // 向队尾增加一个
            return;
        }

        // 声明语句
        if(Production == "declarations -> var declaration semi"){
            return;
        }
        if(Production == "declaration -> declaration semi identifier_list : type"){
            // 将队列中的属性节点依次填入对应的符号表中
            for(unsigned int i = 0; i < attr_node_list.size(); i++)
                enterTable(nowSignTable, attr_node_list[i].name, Stack_attr[attr_top].type,
                            Stack_attr[attr_top].width, (void*)NULL);
            return;
        }
        if(Production == "declaration -> identifier_list : type"){
            // 将队列中的属性节点依次填入对应的符号表中
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
            // 数组类型，使用类型表达式
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

        // 过程和函数声明和定义的翻译
        if(Production == "subprogram_declarations -> @"){
            // 创建新符号表，并将当前符号表更新为此新符号表，同时更新了符号表栈
            nowSignTable = mktable(nowSignTable);
            return;
        }
        if(Production == "parameter_list -> identifier_list : type"){
            // 函数声明时的参数列表
            // 将队列中的属性节点依次填入对应的符号表中
            for(unsigned int i = 0; i < attr_node_list.size(); i++)
                enterTable(nowSignTable, attr_node_list[i].name, Stack_attr[attr_top].type,
                            Stack_attr[attr_top].width, (void*)NULL);
            return;
        }
        if(Production == "subprogram_head -> procedure id arguments semi"){
            // 当前过程声明语句，记录其类型
            nowSignTable->name = Stack_attr[attr_top - 2].name;
            nowSignTable->type = "procedure";
            return;
        }
        if(Production == "subprogram_head -> function id arguments : standard_type semi"){
            // 当前函数声明语句，记录其类型
            nowSignTable->name = Stack_attr[attr_top - 4].name;
            nowSignTable->type = "function";
            nowSignTable->ret_val = Stack_attr[attr_top - 1].type;
            return;
        }
        if(Production == "subprogram_declaration -> subprogram_head declarations compound_statement"){
            // 子过程处理完毕，符号表应退回为上一层,并在 上一层符号表中标记此符号表地址
            NestSignTable *lastTable = nowSignTable->lastTable;
            enterTable(lastTable, nowSignTable->name, nowSignTable->type,
                       4, (void*)nowSignTable);
            table_top--;        // 符号表栈退一层
            nowSignTable = lastTable;       // 指向上一层的符号表
            return;
        }

        // 过程和函数调用的翻译



        // 表达式计算及赋值语句翻译
        // 先进行符号翻译
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
        // 表达式翻译
        if(Production == "variable -> id" || Production == "factor -> id"
           || Production == "term -> factor" || Production == "simple_expression -> term"
           || Production == "expression -> simple_expression"){
            // 赋值语句左值
            int pos = lookup(Stack_attr[attr_top].name);
            // 必须是标识符才报错，因为可能其他的非算数表达式也可能用到这些产生式
            if(pos < 0 && Stack_attr[attr_top].type == "ID"){
                printf("Error:-----Can't find name in SignTable(%s): %s\n",
                        nowSignTable->name.c_str(), Stack_attr[attr_top].name.c_str());
                return;
            }

            ansAttr = Stack_attr[attr_top]; // 将 id 的属性给variable
            return;
        }
        if(Production == "term -> term mulop factor" ||
           Production == "simple_expression -> simple_expression addop term"){
            // 利用括号匹配性质减少临时变量的数量
            if(Stack_attr[attr_top - 2].type == "TempVar") temp_var_cnt--;
            if(Stack_attr[attr_top].type == "TempVar") temp_var_cnt--;
            ansAttr = newtemp();            // 使用临时变量
            gencode(&ansAttr, &Stack_attr[attr_top - 2], &Stack_attr[attr_top - 1],
                    &Stack_attr[attr_top]);
            return;
        }
        if(Production == "statement -> variable assignop expression"){
            // 利用括号匹配性质减少临时变量的数量
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

    // 获取终结符的属性值
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


    // 语法分析过程
    void work(vector<TokenPairType> & word_buf){
        int state, op, now_sign, now_T;
        void *now_T_data;
        vector<pair<int, void*> > now_T_list;   // 存储分析过程中终结符及其数据的序列
        string now_product;
        word_buf.push_back(make_pair(0, (void*)NULL));     // 输入序列后加入 '#'
        attr_top = 0;           // 属性栈清空
        // 创建总的符号表, 并存入栈中
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
                Stack.pop();        // 此时栈恢复到初始状态，方便下一个句子使用
                //printf("Complete sentence number: %d\n", ++sentence_cnt);
                continue;
            }
            if(op == ERROR){
                Error_Handle(i, now_T);
                return;
            }
            // 移进操作
            if(op > 0){
                Stack.push(make_pair(op, now_T));
                Stack_word.push(word_buf[i]);
                // 更新属性栈，并获取其属性
                ++attr_top;

                get_attr_from_T(Stack_attr[attr_top], now_T, now_T_data);
                continue;
            }
            // 归约操作
            now_product = Production[-op];
            //cout << now_product << endl;    // 用这个产生式去归约

            string temp_product = now_product;      // 暂存产生式


            AttrNodeType ansAttr;               // 存储语义分析结果节点
            SemanticAnalysis(temp_product, ansAttr);  // 进行语义分析

            while(true){
                now_sign = get_next_sign(now_product);
                if(now_sign == 0){
                    now_sign = -get_next_sign(now_product); // 归约出的变量
                    state = Stack.top().first;
                    // 根据Goto表转移状态
                    Stack.push(make_pair(Goto[state][now_sign], -now_sign));
                    Stack_word.push(make_pair(0, (void*)NULL));    // 为与Stack保持一致，加入一个空对
                    Stack_attr[++attr_top] = ansAttr;           // 语义属性分析结果入栈
                    i--;        // 此时不能移进终结符

                    // 语义分析相关
//                    cout << temp_product << "   ";
//                    for(unsigned int i = 0; i < now_T_list.size(); i++)
//                        printf("(%d,%s) ", now_T_list[i].first, (char*)now_T_list[i].second);
//                    cout << endl;
                    now_T_list.clear(); // 本次产生式分析完毕，清空临时序列
//                    cout << endl;
                    break;
                }
                if(now_sign == sign_to_num["@"]) continue;  // 空转移
                if(Stack.top().second == now_sign){     // 取出此时的终结符
                    if(Stack.top().second > 0)
                        now_T_list.push_back(Stack_word.top());     // 存储分析此产生式时的终结符序列
                    Stack_word.pop();
                    Stack.pop();
                    attr_top--;         //  语义属性栈弹栈
                }
                else
                    Error_Handle(i, now_sign);
            }
        }
        cout << Production.size() << endl;
        printf("************Syntax Analyze Complete!************\n\n");
    }
};

// 打印所有符号表的内容
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
