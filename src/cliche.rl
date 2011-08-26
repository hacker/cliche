#include <getopt.h>
#include <iostream>
#include <cstring>
#include <cassert>
#include <algorithm>
#include <fstream>

#include "config.h"

struct line_counting_monkey {
	int n;
	const char *p;
	const char *fn;

	line_counting_monkey(const char *fn_,const char *p_) : fn(fn_), n(1), p(p_) { }

	int lineno(const char *pp) {
		if(pp>p) {
			n += std::count(p,pp,'\n');
			p = pp;
		}
		return n;
	}
};

struct code_writing_monkey {
	std::ostream& o;
	enum omode_type {
		om_code = 0, om_output, om_inline, om_literal,
		oms
	};
	omode_type omode;
	int last_anchor, since_anchor;

	code_writing_monkey(std::ostream& o_) : o(o_), omode(om_code), last_anchor(-1), since_anchor(0) { }

	void modify(omode_type om,line_counting_monkey* lcm=0,const char *p=0) {
		static const char *om_transitions[oms][oms] = {
		// To:                                                                            From:
		// code    output                          inline                      literal
		 { "",     "CLICHE_OUTPUT_LITERAL(\n",     "CLICHE_STREAM << (",       "" }, // code
		 { ");\n", "",                             ");\n(CLICHE_STREAM) << (", 0  }, // output
		 { ");\n", ");\nCLICHE_OUTPUT_LITERAL(\n", "",                         0  }, // inline
		 { " ",    0,                              0,                          "" }, // literal
		};
		assert(0 <= omode && omode < oms);
		assert(0 <= om && om < oms);
		const char *t = om_transitions[omode][om];
		assert(t); // TODO: complain?
		o << t;
		since_anchor += std::count(t,t+strlen(t),'\n');
		if(lcm && t && *t && om!=omode && p) anchor(*lcm,p);
		omode = om;
	}

	void prologue() {
		assert(omode==om_code);
		o <<
		"#ifndef CLICHE_STREAM\n"
		"# define CLICHE_STREAM (std::cout)\n"
		"# define CLICHE_STREAM_AUTODEFINED\n"
		"#endif\n"
		"#ifndef CLICHE_OUTPUT_LITERAL\n"
		"# define CLICHE_OUTPUT_LITERAL(sl) (CLICHE_STREAM).write((sl),sizeof(sl)-sizeof(\"\"))\n"
		"#endif\n";
	}
	void epilogue() {
		modify(om_code);
		o << "\n"
		"#ifdef CLICHE_STREAM_AUTODEFINED\n"
		"# undef CLICHE_STREAM\n"
		"# undef CLICHE_STREAM_AUTODEFINED\n"
		"#endif\n";
	}

	void monkey(const char *d,size_t l=0) {
		if(!(l || (l=strlen(d)))) return;
		if(omode!=om_output && omode!=om_literal) {
			since_anchor += std::count(d,d+l,'\n');
			o.write(d,l);
			return;
		}
		o.put('"');
		const char *p=d;
		while(l--) {
			char c;
			switch(*d) {
			case '\r': c='r'; break;
			case '\n': c='n'; break;
			case '\t': c='t'; break;
			case '\a': c='a'; break;
			case '\b': c='b'; break;
			case '\v': c='v'; break;
			case '\f': c='f'; break;
			case '\'': case '\"': case '\\': c=*d; break;
			case 0: c='0'; break;
			default: c=0; break;
			};
			if(!c) {
				++d;
				continue;
			}
			if(p!=d) o.write(p,d-p);
			o.put('\\');
			if(c=='0')
				o.write("000",3);
			else
				o.put(c);
			p=++d;
		}
		if(p!=d) o.write(p,d-p);
		o.write("\"\n",2); ++since_anchor;
	}

	void monkey_as(omode_type om,const char *d,size_t l=0,line_counting_monkey *lcm=0,const char *p=0) { modify(om,lcm,p); monkey(d,l); }

	void anchor(line_counting_monkey& lcm,const char *p) {
		// modify(om_code);
		int l = lcm.lineno(p);
		if(last_anchor>0 && last_anchor+since_anchor==l) return;
		o << "\n#line " << (since_anchor=0,last_anchor=l) << " \"" << lcm.fn << "\"\n";
	}
};


%%{
	machine cliche;

	linebreak = /[\r\n]/;

	action monkey {
		cwm.monkey(ts,te-ts);
	}
	action monkey_code {
		cwm.monkey_as(cwm.om_code,ts,te-ts,&lcm,p);
	}
	action monkey_output {
		cwm.monkey_as(cwm.om_output,ts,te-ts,&lcm,p);
	}
	action monkey_literal {
		cwm.monkey_as(cwm.om_literal,ts,te-ts,&lcm,p);
	}

	slashstar_comment :=
		( any* :>> '*/' ) ${ cwm.monkey(fpc,1); } @{ fret; };

	outputblock := |*
		'%' (^linebreak)* linebreak { cwm.monkey_as(cwm.om_code,ts+1,te-ts-1,&lcm,p); };
		 any=> { fhold; fcall outputline; };
		
	*|;
	outputline := |*
		(^linebreak)* linebreak -- ('</%output>' | '<%code>' | ('<%' space) ) { cwm.monkey_as(cwm.om_output,ts,te-ts,&lcm,p); fret; };
		'<%code>' { cwm.modify(cwm.om_code,&lcm,p); fcall codeblock; };
		'</%output>' { --top; fret; };
		'<%' space { cwm.modify(cwm.om_inline,&lcm,p); fcall inlineblock; };
		(^linebreak)+ -- ( '%' | '<' ) => monkey_output;
		any => monkey_output;
	*|;

	inlineblock := |*
		space '%>' { cwm.modify(cwm.om_code,&lcm,p); fret; };
		"'" ( [^'\\] | /\\./ )* "'" => monkey;
		'"' ( [^"\\] | /\\./ )* '"' => monkey;
		'/*' { cwm.monkey("/*",2); fcall slashstar_comment; };
		'//' (^linebreak)* (linebreak) => monkey;
		any => monkey;
	*|;

	literalblock := |*
		any => { fhold; fcall literalline; };
	*|;
	literalline := |*
		(^linebreak)* linebreak -- ('</%literal>' | ('<%' space) ) { cwm.monkey_as(cwm.om_literal,ts,te-ts,&lcm,p); fret; };
		'</%literal>' { --top; fret; };
		'<%' space { cwm.modify(cwm.om_code,&lcm,p); fcall inlineblock; };
		(^linebreak)+ -- ( '%' | '<' ) => monkey_literal;
		any => monkey_literal;
	*|;

	codeblock := |*
		'<%output>'	{ fcall outputblock; };
		'<%literal>'	{ fcall literalblock; };
		'</%code>'	{ fret; };
		"'" ( [^'\\] | /\\./ )* "'" => monkey_code;
		'"' ( [^"\\] | /\\./ )* '"' => monkey_code;
		'/*' { cwm.monkey("/*",2); fcall slashstar_comment; };
		'//' (^linebreak)* (linebreak) => monkey_code;
		any => monkey_code;
	*|;

	main :=  any >{
		fhold;
		switch(topmode) {
		case code_writing_monkey::om_output: fgoto outputblock;
		case code_writing_monkey::om_code: fgoto  codeblock;
		default: ;/* TODO: WTD? */
		};
	};
}%%

%% write data;

static const char *biname = 0;
static void display_usage() {
	std::cerr << PACKAGE " Version " VERSION "\n"
	"Copyright (c) 2011 Klever Group\n"
	"\n"
	" " << biname << " [otpions] [input-file]\n"
	"\n"
#ifdef HAVE_GETOPT_LONG
	" -h, --help\n"
	" --usage                     display this text\n"
	" -V, --version               display version number\n"
	" -L, --license               show license\n"
	" -o <file>, --output=<file>  write output to the named file\n"
	" -t code|output, --top=code|output\n"
#else
	" -h                          display this text\n"
	" -V                          display version number\n"
	" -L                          show license\n"
	" -o <file>                   write output to the named file\n"
	" -t code|output\n"
#endif
	"                             set toplevel processing mode [output]\n"
	" -C                          same as -t=code\n"
	" -O                          same as -t=output (default)\n"
	"\n";
}

int main(int argc,char *argv[]) {
	biname = *argv;
	std::string ofile;
	code_writing_monkey::omode_type topmode = code_writing_monkey::om_output;
	while(true) {
		static const char shopts[] = "hVLo:t:CO";
#if HAVE_GETOPT_LONG
		static struct option opts[] = {
			{ "help", no_argument, 0, 'h' },
			{ "usage", no_argument, 0, 'h' },
			{ "version", no_argument, 0, 'V' },
			{ "license", no_argument, 0, 'L' },
			{ "output", required_argument, 0, 'o' },
			{ "top", required_argument, 0, 't' },
			{ NULL, 0, 0, 0 }
		};
		int c = getopt_long(argc,argv,shopts,opts,NULL);
#else
		int c = getopt(argc,argv,shopts);
#endif
		if(c==-1) break;
		switch(c) {
		case 't':
			if(!strcasecmp(optarg,"code")) {
				topmode = code_writing_monkey::om_code;
				break;
			}else if(!strcasecmp(optarg,"output")) {
				topmode = code_writing_monkey::om_output;
				break;
			}
			std::cerr << "Unkown '" << optarg << "' mode" << std::endl;
		case '?': /* unknown option */
		case 'h': display_usage(); exit(0); break;
		case 'V': std::cerr << VERSION << std::endl; exit(0); break;
		case 'L':
			extern const char *COPYING;
			std::cerr << COPYING << std::endl;
			exit(0); break;
		case 'o': ofile = optarg; break;
		case 'C': topmode = code_writing_monkey::om_code; break;
		case 'O': topmode = code_writing_monkey::om_output; break;
		default:
			std::cerr << "Huh?" << std::endl;
			exit(1); break;
		}
	}
#undef LS
	if((optind+1)!=argc) {
		display_usage(); exit(1);
		/* TODO: or use stdin if no parameter specified? */
	}

	std::string ifile = argv[optind];
	if(ofile.empty()) ofile = ifile+".cc";
	std::ifstream ist(ifile.c_str(),std::ios::in);
	std::ofstream ost(ofile.c_str(),std::ios::out);
	if(!ost) {
		std::cerr << "failed to open '" << ofile << "' for writing" << std::endl;
		exit(2);
	}

	int cs, act;
	char *ts, *te;
	int stack[128], top=0;
	%% write init;
	char input[512];
	int have = 0;
	char *eof = 0;
	code_writing_monkey cwm(ost);
	cwm.prologue();
	line_counting_monkey lcm(ifile.c_str(),input);
	cwm.anchor(lcm,0);
	while(!eof) {
		if(have==sizeof(input)) {
			std::cerr << "No space to read in" << std::endl;
			break;
		}
		char *p = input+have;
		int lw = sizeof(input)-have;
		int lp = ist.read(p,lw).gcount();
		char *pe = p+lp;
		eof = (lp==lw)?0:pe;
		%%write exec;
		if(cs==cliche_error) {
			std::cerr << "cliche error" << std::endl;
			break;
		}
		if(ts) {
			lcm.lineno(ts);
			te = ((char*)memmove(input,ts,have=pe-ts)) + (te-ts);
			ts = input;
		}else{
			lcm.lineno(pe);
			have = 0;
		}
		lcm.p = input;
	}
	cwm.epilogue();
	return 0;
}
/* vim:set ft=ragel ts=8 sw=8 cin si ai: */
