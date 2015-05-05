#!/usr/bin/sudo /usr/bin/node
// Simple DNS Poisoning Proxy
// written by: Kiswono Prayogo (2011-2012)
/*
// DS object
var lib = require('./build/default/ndns');
var server = new lib.NDNS();
server.fWoCallback();
server.fWCallback(function(e){
  console.log(e);
});
*/
/**
 * @name config object
 * @description dns server configuration
*/
var config = {
  bindPort: 53
, poisonIPv4: [ 127, 0, 0, 1 ]
//, dnsForwardIP: '192.168.11.150' //'4.2.2.1' //'8.8.8.8'
, dnsForwardIP: '4.2.2.1'
//, dnsForwardIP: '8.8.8.8'
, dnsForwardPort: 53
, loadBlacklist: '' // 'blacklist.txt'
, debugMode: false
, verboseMode: true
, exitPassphrase: 'doExitServer.'
}

var inspect = require('util').inspect;

/**
 * @name autocomplete and value helpers
*/
var arguments = { callee : { name : '' } };
var b11000000 = parseInt('11000000',2);
var b10000000 = parseInt('10000000',2);
var b01111000 = parseInt('01111000',2);
var b00000100 = parseInt('00000100',2);
var b00000010 = parseInt('00000010',2);
var b11111101 = parseInt('11111101',2);
var b00000001 = parseInt('00000001',2);
var b01110000 = parseInt('01110000',2);
var b00001111 = parseInt('00001111',2);
var b00111111 = parseInt('00111111',2);

/**
 * @name d object
 * @description debug and pretty print object
*/
var d = {
  level : 0
, calls : 0
, buffer : 
  [ ' '
  , '   '
  , '     '
  , '       '
  , '         '
  , '           '
  , '             '
  ]
, fixedPad : function() {
    process.stdout.write(this.buffer[this.level]);
  }
, zeroPad : function(str,max,padder) {
    if(!padder) padder = '0';
    if(!max) max = 2;
    if(!str) str = '' + padder;
    str = str + '';
    while(str.length<max) str = '' + padder + str;
    return str;
  }
, log : function(things) {
    if(config.debugMode) {
      this.fixedPad();
      console.log(things);          
    }
  }  
, logJson : function(things) {
    if(config.debugMode) {
      this.fixedPad();
      console.log(JSON.stringify(things));
    }
  }  
, logBin : function(buff) {  
    var start = 0;
    var line = 0;
    this.log('      00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31');
    str = '000 > ';
    while(start<buff.length) {
      str += buff.toString('hex',start,start+1) + ' ';
      ++start;
      if(0==start%32) {
        this.log(str);
        line+=32;
        str = this.zeroPad(line,3) + ' > ';
      }
    }
    if(str) d.log(str);
  }
, beginFunction : function(funcName) {
    if(config.debugMode) {
      ++this.calls;
      this.fixedPad();
      ++this.level;
      console.log('>> '+funcName+' BEGIN ');
    }
  }
, endFunction : function (funcName,ret) {
    if(config.debugMode) {
      --this.level;
      this.fixedPad();
      console.log('<< '+funcName+' END ');
    }
    return ret;
  }
, abortFunction : function (funcName,reason) {  
    if(config.debugMode) {
      --this.level;
      this.fixedPad();
      console.log('<< '+funcName+' FAILURE END '+JSON.stringify(arguments));
    }
    return false;
  }
}

/**
 * @name parseCNAME
 * @returns 1 + last read index, 0 if error (should be equal to end)
 * @param start (in), parsing start index
 * @param buff (in), packet Buffer
 * @param compression (in out), index and label { cidx: NAME }
 * @param name (out), NAME object { name, type, class }
*/

function parseCNAME(start,buff,compression,name,end) {
  d.beginFunction(arguments.callee.name);
  if(!end) end = buff.length;
  var session = [];
  while(true) {
    var howMany = buff[start];
    if(!howMany) { // label terminator
      ++start;
      break;
    } else if(howMany & b11000000) { // dns compression
      var position = (howMany & b00111111) * 256 + buff[start+1] ;
      var label = compression[position];
      if(!label) return d.abortFunction(arguments.callee.name,'invalid pointer',position,compression);
      session.push([start,label])
      start += 2;
      break;
    } else { // 1-byte length, n-byte chars      
      if(start+howMany>=end) return d.abortFunction(arguments.callee.name,'index out of range ',start,howMany,end,session);
      ++howMany;
      var label = '';
      for(var z=start+1;z<start+howMany;++z) {
        label += String.fromCharCode(buff[z]);
      }
      label += '.';
      session.push([start,label]);
      start += howMany;
    }        
  }
  var idxList = [];
  for(var sidx in session) {
    var posLabelPair = session[sidx];
    var label = posLabelPair[1];
    for(var pidx in idxList) {
      var cidx = idxList[pidx];
      compression[cidx] += label;
    }
    var cidx = posLabelPair[0];
    compression[cidx] = label;
    idxList.push(cidx);
  }
  if(!idxList.length) return d.abortFunction(arguments.callee.name,'zero length label')
  name.name = compression[idxList[0]];
  return d.endFunction(arguments.callee.name,start);
}

/**
 * @name parseNAME
 * @returns 1 + last read index, 0 if error
 * @param start (in), parsing start index
 * @param buff (in), packet Buffer
 * @param compression (in out), index and label { cidx: NAME }
 * @param name (out), NAME object { name, type, class }
*/
function parseNAME(start,buff,compression,name) {
  d.beginFunction(arguments.callee.name);
  var end = buff.length;
  /* QNAME, sama seperti NAME. 
   * NAME (n oktet) nama domain.*/
  start = parseCNAME(start,buff,compression,name);
  if(!start) return d.abortFunction(arguments.callee.name,'invalid name')
  if(start+4>end) return d.abortFunction(arguments.callee.name,'index out of range');
  /* QTYPE (2 oktet), yang dapat bernilai sama seperti TYPE atau:
    * 252 = AXFR, permintaan untuk mentransfer semua isi zone.
    * 255 = *, meminta semua jenis RR.
   * TYPE (2 oktet) tipe RR, yang dapat bernilai:
    * 1 = A, alamat IPv4.
    * 2 = NS, authoritative NS.
    * 5 = CNAME, alias.
    * 6 = SOA, awal dari zone of authority.
    * 12 = PTR, penunjuk nama domain.
    * 15 = MX, mail exchange.
    * 16 = TXT, text string.
    * 28 = AAAA, alamat IPv6.*/    
  name.type = buff[start] * 256 + buff[start+1];
  start += 2;
  /* QCLASS (2 oktet), yang dapat bernilai sama seperti TYPE atau:
    * 255 = *, class apapun.
   * CLASS (2 oktet) kelas RR, yang dapat bernilai:
    * 1 = IN, internet.
    * 3 = CH, chaos.   */
  name['class'] = buff[start] * 256 + buff[start+1];
  start += 2;
  d.logJson(name);
  return d.endFunction(arguments.callee.name,start);
}

/**
 * @name parseHEADER
 * @returns HEADER object, 0 if error
 * @param buff (in), packet Buffer
*/
function parseHEADER(buff) {
  d.beginFunction(arguments.callee.name);
  var header = {};
  // HEADER
  if(buff.length<12) return d.abortFunction(arguments.callee.name,'index out of range');  
  /* ID (16-bit) digenerate oleh requester. */
  header.ID = buff[0]*256+buff[1];
  d.log('ID '+header.ID);  
  /* QR (1-bit) 0 = query, 1 = response. */
  header.QR = (buff[2] & b10000000) >> 7;
  d.log('QR (0=QUERY,1=RESPONSE) '+header.QR);
  /* OPCODE (4-bit) jenis query, yang dapat bernilai:
    * 0 = QUERY.
    * 1 = IQUERY (inverse query).
    * 2 = STATUS (status server). */
  header.OPCODE = (buff[2] & b01111000) >> 3;
  d.log('OPCODE (0=QUERY,1=IQUERY,2=STATUS) '+header.OPCODE);
  /* AA (1-bit) authoritative answer. */
  header.AA = (buff[2] & b00000100) >> 2;
  d.log('AA (is authoritative answer?) '+header.AA);
  /* TC (1-bit) truncated, apakah pesan terpotong. */
  header.TC = (buff[2] & b00000010) >> 1;
  d.log('TC (is truncated?) '+header.TC);
  /* RD (1-bit) recursive desired, menanyakan apakah NS support recursive query. */
  header.RD = (buff[2] & b00000001);
  d.log('RD (is recursive desired?) '+header.RD);
  /* RA (1-bit) recursive available, NS mensupport recursive query. */
  header.RA = (buff[3] & b10000000) >> 7;
  d.log('RA (is recursive available?) '+header.RA);
  /* Z (3-bit) reserved, harus bernilai 0. */
  header.Z  = (buff[3] & b01110000) >> 4;
  d.log('Z (0=reserved) '+header.Z);
  /* RC (4-bit) response code, yang dapat bernilai:
    * 0 = no error.
    * 1 = query format error.
    * 2 = server failure.
    * 3 = name error, khusus authoritative bahwa nama domain tidak ada.
    * 4 = not implemented.
    * 5 = refused */ 
  header.RC = (buff[3] & b00001111);
  d.log('RC (0=noErr,1=formatErr,2=servFail,3=nameErr,4=notImpl,5=refused) '+header.RC);
  /* QDCOUNT, ANCOUNT, NSCOUNT, ARCOUNT (16-bit unsigned integer) jumlah RR pada bagian question, answer, authority dan additional. */    
  header.QDCOUNT = buff[4]*256 + buff[5];
  header.ANCOUNT = buff[6]*256 + buff[7];
  header.NSCOUNT = buff[8]*256 + buff[9];
  header.ARCOUNT = buff[10]*256 + buff[11];
  d.log('QD/AN/NS/AR COUNT '+header.QDCOUNT+' '+header.ANCOUNT+' '+header.NSCOUNT+' '+header.ARCOUNT);
  return d.endFunction(arguments.callee.name,header);
}

/**
 * @name parseRR
 * @returns RR object
 * @param start (in), parsing start index
 * @param buff (in), packet Buffer
 * @param compression (in out), index and label { cidx: NAME }
 * @param rr (in), RR object
*/
function parseRR(start,buff,compression,rr) {
  d.beginFunction(arguments.callee.name);
  var end = buff.length;
  var name = {};
  start = parseNAME(start,buff,compression,name);
  if(!start) return d.abortFunction(arguments.callee.name,'invalid labels');
  rr.NAME = name;
  if(start+6>end) return d.abortFunction(arguments.callee.name,'index out of range');  
  /* TTL (32-bit signed integer) durasi cache.*/
  //config.debugMode = true;
  //d.logBin(buff);
  //console.log(buff);
  //console.log(buff.length);
  //console.log(start);
  rr.TTL = buff.readInt32BE(start)  // SOLVED: error at 0.6.1, no error at 0.6.2
  start += 4;
  /* RDLENGTH (16 bit integer) panjang RDATA.*/
  rr.RDLENGTH = buff.readUInt16BE(start);
  start += 2;
  if(start+rr.RDLENGTH>end) return d.abortFunction(arguments.callee.name,'index out of range');
  var data = {};
  switch(name.type) {
    case 1: // = A, alamat IPv4.
      if(rr.RDLENGTH!=4) return d.abortFunction(arguments.callee.name,'invalid rdlength');     
      var ip = buff.readUInt32BE(start);
      data.integer = ip
      data.string = Math.floor(ip/16777216)%256 + '.' + Math.floor(ip/65536)%256 + '.' + Math.floor(ip/256)%256 + '.' + (ip%256);
      break;
    case 5: // = CNAME, alias.
      var bRead = parseCNAME(start,buff,compression,data,start+rr.RDLENGTH);
      if(bRead!=start+rr.RDLENGTH) return d.abortFunction(arguments.callee.name,'invalid cname rd');      
      break;
    case 2: // = NS, authoritative NS.
    case 6: // = SOA, awal dari zone of authority.
    case 12: // = PTR, penunjuk nama domain.
    case 15: // = MX, mail exchange.
    case 16: // = TXT, text string.
    case 28: // = AAAA, alamat IPv6.
    default:
      // TODO: jenis lain (di luar ruang lingkup)
      // d.log('unknown rrtype: '+name.type)
      data = buff.toString('hex',start,start+rr.RDLENGTH);
      break;
  }
  start += rr.RDLENGTH;
  rr.DATA = data;
  d.logJson(rr);
  return d.endFunction(arguments.callee.name,start);
}

/**
 * @name parsePACKET
 * @param buff, packet Buffer
*/
function parsePACKET(buff) {
  d.beginFunction(arguments.callee.name);
  var packet = { buffer: buff };
  // HEADER
  var header = parseHEADER(buff);
  
  if(!header) return d.abortFunction(arguments.callee.name,'invalid header');
  packet.header = header;
  var bParsed = 12;
  var compressions = {};
  // QUESTIONS
  var questions = [];
  for(var z=0;z<header.QDCOUNT;++z) {
    var name = {};
    bParsed = parseNAME(bParsed,buff,compressions,name);
    if(!bParsed) return d.abortFunction(arguments.callee.name,'invalid labels');
    questions.push(name);
  }
  // ANSWERS
  var answers = [];
  for(var z=0;z<header.ANCOUNT;++z) {
    var rr = {};
    bParsed = parseRR(bParsed,buff,compressions,rr);
    if(!bParsed) return d.abortFunction(arguments.callee.name,'invalid answers');
    answers.push(rr);
  }
  // AUTHORITIES
  var authorities = [];
  for(var z=0;z<header.NSCOUNT;++z) {
    var rr = {}; 
    bParsed = parseRR(bParsed,buff,compressions,rr);
    if(!bParsed) return d.abortFunction(arguments.callee.name,'invalid authorities');
    authorities.push(rr);
  }
  // ADDITIONALS
  var additionals = [];
  for(var z=0;z<header.ARCOUNT;++z) {
    var rr = {}; 
    bParsed = parseRR(bParsed,buff,compressions,rr);
    if(!bParsed) return d.abortFunction(arguments.callee.name,'invalid additionals');
    additionals.push(rr);
  }
  packet.questions = questions;
  packet.compressions = compressions;
  packet.answers = answers;
  packet.authorities = authorities;
  packet.additionals = additionals;
  d.log(inspect(packet,false,3));
  return d.endFunction(arguments.callee.name,packet);
}

var fs = require('fs');
var tdict =
{ data : {}
, insert: function(domain) {
    var labels = domain.split('.');
    var next = this.data;
    var label = '';
    for(var z=labels.length-1;z>=0;--z) {
      label = labels[z];
      if(label=='') continue;
      if(!next) break;
      if(!next[label]) next[label] = {};
      if(z==0) next[label] = true; else next = next[label];
    }
  }
, load: function(fileName) {
    if(!this.data) this.data = {};
    console.log('loading dictionary',fileName);
    var txt = fs.readFileSync(fileName,'utf8');
    txt = txt.split('\n');
    var st = new Date();
    for(var i in txt) {
      var domain = txt[i];
      if(domain) this.insert(domain);
    }
    var ft = new Date();
    console.log('blacklist loaded in',(ft-st)/1000," s");
  }
, find: function(domain) {
    var labels = domain.split('.').reverse();
    labels.shift();
    var next = this.data;
    for(var i in labels) {
      var label = labels[i];
      if(!next) return null;
      if(next[label]==true) return true; else next = next[label];
    }
    return false;
  }
}
if(config.loadBlacklist) tdict.load(config.loadBlacklist);
var tcache = {};
//var lib = require('./build/default/ndns');
//var storage = new lib.NDNS();
// TODO: sambungkan ke C++ (di luar ruang lingkup)
var dgram = require('dgram');
var recursor = require('dns');
var server = dgram.createSocket('udp4');
var requests = {};
server
  .on("message", function (msg, rinfo) {
    d.beginFunction('server.on("message")');
    d.logJson(rinfo);
    d.logBin(msg);
    var request = parsePACKET(msg);
    if(request && request.questions && request.questions.length) {
      var question = request.questions[0];
      var domain = question.name; // TODO: cari contoh paket yg questionnya > 1 (dig dan nslookup g bisa)
      var dclass = question['class'];
      var dtype = question.type;
      if(domain==config.exitPassphrase) server.close();
      if(request.header.QR || request.answers && request.answers.length) { // response from higher dns server
        if(config.verboseMode) console.log('response > '+domain);
        if(requests[request.header.ID] && requests[request.header.ID][domain]) {
          // caching
          var time = new Date();
          var minTTL = 60*60*24*7;
          for(var z in request.answers) {
            var newTTL = request.answers[z].TTL; 
            if(minTTL>newTTL) minTTL=newTTL;
          }
          time.setSeconds(time.getSeconds()+minTTL);
          request.buffer[2] &= b11111101;
          if(request.answers && request.answers.length) {
            tcache[domain+' '+dclass+' '+dtype] = { time : time, buffer: request.buffer }
          }
          var req = requests[request.header.ID][domain];
          server.send(request.buffer,0,request.buffer.length,req.rinfo.port,req.rinfo.address);
          // delete responded request
          delete requests[request.header.ID][domain];
          var count = false;
          for(var v in requests[request.header.ID]) {
            count = true;
            break;
          }
          if(!count) delete request[request.header.ID];
        }
      } else { // request from client
        if(config.verboseMode) console.log('request < '+rinfo.address+':'+rinfo.port+' > '+domain);
        // TODO: ganti tdict dengan storage (di luar ruang lingkup)          
        if(tdict.find(domain)) { // blacklisted
          // respond with forged result
          // TODO: query lain, MX (di luar ruang lingkup)
          var len = 12;
          for(var z in request.questions) len += request.questions[z].name.length + 5;
          var forged = new Buffer(len+16);
          request.buffer.copy(forged,0,0,len);
          forged[2] = 0x85; // set as reply
          forged[3] = 0; // disable recursive
          forged[6] = 0; // respond with one (A)
          forged[7] = 1;
          forged[8] = 0; // hide ns history
          forged[9] = 0;
          forged[10] = 0; // hide auth
          forged[11] = 0;
          forged[len++] = 0xC0; // ptr ke request 1
          forged[len++] = 0x0C; 
          forged[len++] = 0; // type 1
          forged[len++] = 1;
          forged[len++] = 0; // class 1
          forged[len++] = 1;
          forged[len++] = 0; // ttl 60
          forged[len++] = 0;
          forged[len++] = 0;
          forged[len++] = 0x3c;
          forged[len++] = 0; // rdata len 4
          forged[len++] = 4;
          var pi = config.poisonIPv4;
          forged[len++] = pi[0]; // poisoned ipv4
          forged[len++] = pi[1];
          forged[len++] = pi[2];
          forged[len++] = pi[3];
          server.send(forged,0,forged.length,rinfo.port,rinfo.address);
          if(config.verboseMode) console.log('forged '+domain);
        } else {
          var cache = tcache[domain+' '+dclass+' '+dtype];
          if(cache && cache.time > new Date()) {
            if(config.verboseMode) console.log('cache > '+domain);
            cache.buffer[0] = request.buffer[0];
            cache.buffer[1] = request.buffer[1];
            server.send(cache.buffer,0,cache.buffer.length,rinfo.port,rinfo.address);
          } else {
            delete cache;
            server.send(msg,0,msg.length,config.dnsForwardPort,config.dnsForwardIP);
            if(!requests[request.header.ID]) requests[request.header.ID] = {};
            requests[request.header.ID][domain] = { rinfo: rinfo, request: request }            
          }
        }
      }
    }
    d.endFunction('server.on("message")');
  })
  .on("listening", function () {
    d.beginFunction('server.on("listening")');
    d.logJson(server.address());
    d.endFunction('server.on("listening")');
  })
  .on("close", function() {
    if(config.verboseMode) {
      for(var dom in tcache) console.log(dom);
    }
  })
  .bind(config.bindPort);
  console.log('server ready!');
  // sudo iptables -t nat -A PREROUTING -p tcp --dport 53 -j REDIRECT --to-ports 1053 # dari luar
  
  
  
  /*
  // REQUEST example
  byte     0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27
             
  dig @127.0.0.1 -p 1053 google.com -t A
  
  <Buffer 7a 7c 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01>
  <Buffer 77 67 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01>
  <Buffer 62 34 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01>
  
  echo 'lserver 127.1
  set port=1053
  google.com' | nslookup
  
  <Buffer 69 1f 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01>
  <Buffer 56 93 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01>
  <Buffer b2 02 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01>
  
  // RESPONSE example  
  byte     0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50
  
  <Buffer cc 57 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 0f 00 01>
  <Buffer cc 57 81 80 00 01 00 05 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 0f 00 01 c0 0c 00 0f 00 01 00 00 02 53 00 11 00 28 04 61 6c 74 33 05 61 73 70 ...>
  
  <Buffer 95 56 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01>
  <Buffer 95 56 81 80 00 01 00 05 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01 c0 0c 00 01 00 01 00 00 01 2c 00 04 4a 7d eb 32 c0 0c 00 01 00 01 00 ...>
    
         00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
   000 >[56 3e 81 80|00 01|00 06|00 00|00 00[03 77 77 77|06 67 6f 6f 67 6c 65|03 63 6f 6d|00]00 01|00 01|
   032 >[c0 0c]00 05|00 01|00 01 51 7f|00 08|03 77 77 77 01 6c c0 10|c0 2c 00 01 00 01 00 00 01 2b 00 04 
   064 > 4a 7d eb 30 c0 2c 00 01 00 01 00 00 01 2b 00 04 4a 7d eb 34 c0 2c 00 01 00 01 00 00 01 2b 00 04 
   096 > 4a 7d eb 33 c0 2c 00 01 00 01 00 00 01 2b 00 04 4a 7d eb 31 c0 2c 00 01 00 01 00 00 01 2b 00 04 
   128 > 4a 7d eb 32]
   
  www.google.com.                        IN      A
  www.google.com.         86399   IN      CNAME   www.l.google.com.
  www.l.google.com.       299     IN      A       74.125.235.48
  www.l.google.com.       299     IN      A       74.125.235.51
  www.l.google.com.       299     IN      A       74.125.235.50
  www.l.google.com.       299     IN      A       74.125.235.52
  www.l.google.com.       299     IN      A       74.125.235.49


  // BOTH normal operation example
 
 {"size":28,"address":"127.0.0.1","port":15526}
       00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
 000 > aa 1c 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01 
 ID 43548
 QR (0=QUERY,1=RESPONSE) 0
 OPCODE (0=QUERY,1=IQUERY,2=STATUS) 0
 AA (is authoritative answer?) 0
 TC (is truncated?) 0
 RD (is recursive desired?) 1
 RA (is recursive available?) 0
 Z (0=reserved) 0
 RC (0=noErr,1=formatErr,2=servFail,3=nameErr,4=notImpl,5=refused) 0
 QD/AN/NS/AR COUNT 1 0 0 0
 {"name":"google.com.","type":1,"class":1}
 { buffer: <Buffer aa 1c 01 00 00 01 00 00 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01>,
  header: 
   { ID: 43548,
     QR: 0,
     OPCODE: 0,
     AA: 0,
     TC: 0,
     RD: 1,
     RA: 0,
     Z: 0,
     RC: 0,
     QDCOUNT: 1,
     ANCOUNT: 0,
     NSCOUNT: 0,
     ARCOUNT: 0 },
  questions: [ { name: 'google.com.', type: 1, class: 1 } ],
  compressions: { '12': 'google.com.', '19': 'com.' },
  answers: [],
  authorities: [],
  additionals: [] }
request from client


 {"size":108,"address":"8.8.8.8","port":53}
       00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
 000 > aa 1c 81 80 00 01 00 05 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01 c0 0c 00 01 
 032 > 00 01 00 00 01 2c 00 04 4a 7d eb 32 c0 0c 00 01 00 01 00 00 01 2c 00 04 4a 7d eb 31 c0 0c 00 01 
 064 > 00 01 00 00 01 2c 00 04 4a 7d eb 34 c0 0c 00 01 00 01 00 00 01 2c 00 04 4a 7d eb 30 c0 0c 00 01 
 096 > 00 01 00 00 01 2c 00 04 4a 7d eb 33 
 ID 43548
 QR (0=QUERY,1=RESPONSE) 1
 OPCODE (0=QUERY,1=IQUERY,2=STATUS) 0
 AA (is authoritative answer?) 0
 TC (is truncated?) 0
 RD (is recursive desired?) 1
 RA (is recursive available?) 1
 Z (0=reserved) 0
 RC (0=noErr,1=formatErr,2=servFail,3=nameErr,4=notImpl,5=refused) 0
 QD/AN/NS/AR COUNT 1 5 0 0
 {"name":"google.com.","type":1,"class":1}
 {"name":"google.com.","type":1,"class":1}
 {"NAME":{"name":"google.com.","type":1,"class":1},"TTL":300,"RDLENGTH":4,"DATA":{"integer":1249766194,"string":"74.125.235.50"}}
 {"name":"google.com.","type":1,"class":1}
 {"NAME":{"name":"google.com.","type":1,"class":1},"TTL":300,"RDLENGTH":4,"DATA":{"integer":1249766193,"string":"74.125.235.49"}}
 {"name":"google.com.","type":1,"class":1}
 {"NAME":{"name":"google.com.","type":1,"class":1},"TTL":300,"RDLENGTH":4,"DATA":{"integer":1249766196,"string":"74.125.235.52"}}
 {"name":"google.com.","type":1,"class":1}
 {"NAME":{"name":"google.com.","type":1,"class":1},"TTL":300,"RDLENGTH":4,"DATA":{"integer":1249766192,"string":"74.125.235.48"}}
 {"name":"google.com.","type":1,"class":1}
 {"NAME":{"name":"google.com.","type":1,"class":1},"TTL":300,"RDLENGTH":4,"DATA":{"integer":1249766195,"string":"74.125.235.51"}}
 { buffer: <Buffer aa 1c 81 80 00 01 00 05 00 00 00 00 06 67 6f 6f 67 6c 65 03 63 6f 6d 00 00 01 00 01 c0 0c 00 01 00 01 00 00 01 2c 00 04 4a 7d eb 32 c0 0c 00 01 00 01 00 ...>,
  header: 
   { ID: 43548,
     QR: 1,
     OPCODE: 0,
     AA: 0,
     TC: 0,
     RD: 1,
     RA: 1,
     Z: 0,
     RC: 0,
     QDCOUNT: 1,
     ANCOUNT: 5,
     NSCOUNT: 0,
     ARCOUNT: 0 },
  questions: [ { name: 'google.com.', type: 1, class: 1 } ],
  compressions: 
   { '12': 'google.com.',
     '19': 'com.',
     '28': 'google.com.',
     '44': 'google.com.',
     '60': 'google.com.',
     '76': 'google.com.',
     '92': 'google.com.' },
  answers: 
   [ { NAME: { name: 'google.com.', type: 1, class: 1 },
       TTL: 300,
       RDLENGTH: 4,
       DATA: { integer: 1249766194, string: '74.125.235.50' } },
     { NAME: { name: 'google.com.', type: 1, class: 1 },
       TTL: 300,
       RDLENGTH: 4,
       DATA: { integer: 1249766193, string: '74.125.235.49' } },
     { NAME: { name: 'google.com.', type: 1, class: 1 },
       TTL: 300,
       RDLENGTH: 4,
       DATA: { integer: 1249766196, string: '74.125.235.52' } },
     { NAME: { name: 'google.com.', type: 1, class: 1 },
       TTL: 300,
       RDLENGTH: 4,
       DATA: { integer: 1249766192, string: '74.125.235.48' } },
     { NAME: { name: 'google.com.', type: 1, class: 1 },
       TTL: 300,
       RDLENGTH: 4,
       DATA: { integer: 1249766195, string: '74.125.235.51' } } ],
  authorities: [],
  additionals: [] }
response from server

  // BOTH forged operation example
  
   {"size":25,"address":"127.0.0.1","port":22904}
       00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
 000 > e9 67 01 00 00 01 00 00 00 00 00 00 07 67 65 6e 65 73 69 73 00 00 01 00 01 
 ID 59751
 QR (0=QUERY,1=RESPONSE) 0
 OPCODE (0=QUERY,1=IQUERY,2=STATUS) 0
 AA (is authoritative answer?) 0
 TC (is truncated?) 0
 RD (is recursive desired?) 1
 RA (is recursive available?) 0
 Z (0=reserved) 0
 RC (0=noErr,1=formatErr,2=servFail,3=nameErr,4=notImpl,5=refused) 0
 QD/AN/NS/AR COUNT 1 0 0 0
 {"name":"genesis.","type":1,"class":1}
 { buffer: <Buffer e9 67 01 00 00 01 00 00 00 00 00 00 07 67 65 6e 65 73 69 73 00 00 01 00 01>,
  header: 
   { ID: 59751,
     QR: 0,
     OPCODE: 0,
     AA: 0,
     TC: 0,
     RD: 1,
     RA: 0,
     Z: 0,
     RC: 0,
     QDCOUNT: 1,
     ANCOUNT: 0,
     NSCOUNT: 0,
     ARCOUNT: 0 },
  questions: [ { name: 'genesis.', type: 1, class: 1 } ],
  compressions: { '12': 'genesis.' },
  answers: [],
  authorities: [],
  additionals: [] }
     
request from client
 {"size":57,"address":"192.168.1.254","port":53}
       00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
 000 > e9 67|85 80|00 01.00 02.00 00.00 00|07 67 65 6e 65 73 69 73 00 00 01 00 01|c0 0c.00 01.00 01.00 
 032 > 00 00 3c.00 04.7f 00 00 01.c0 0c 00 01 00 01 00 00 00 3c 00 04 ca 89 07 ea 
 ID 59751
 QR (0=QUERY,1=RESPONSE) 1
 OPCODE (0=QUERY,1=IQUERY,2=STATUS) 0
 AA (is authoritative answer?) 1
 TC (is truncated?) 0
 RD (is recursive desired?) 1
 RA (is recursive available?) 1
 Z (0=reserved) 0
 RC (0=noErr,1=formatErr,2=servFail,3=nameErr,4=notImpl,5=refused) 0
 QD/AN/NS/AR COUNT 1 2 0 0
 {"name":"genesis.","type":1,"class":1}
 {"name":"genesis.","type":1,"class":1}
 {"NAME":{"name":"genesis.","type":1,"class":1},"TTL":60,"RDLENGTH":4,"DATA":{"integer":2130706433,"string":"127.0.0.1"}}
 {"name":"genesis.","type":1,"class":1}
 {"NAME":{"name":"genesis.","type":1,"class":1},"TTL":60,"RDLENGTH":4,"DATA":{"integer":3397978090,"string":"202.137.7.234"}}
 { buffer: <Buffer e9 67 85 80 00 01 00 02 00 00 00 00 07 67 65 6e 65 73 69 73 00 00 01 00 01 c0 0c 00 01 00 01 00 00 00 3c 00 04 7f 00 00 01 c0 0c 00 01 00 01 00 00 00 3c ...>,
  header: 
   { ID: 59751,
     QR: 1,
     OPCODE: 0,
     AA: 1,
     TC: 0,
     RD: 1,
     RA: 1,
     Z: 0,
     RC: 0,
     QDCOUNT: 1,
     ANCOUNT: 2,
     NSCOUNT: 0,
     ARCOUNT: 0 },
  questions: [ { name: 'genesis.', type: 1, class: 1 } ],
  compressions: 
   { '12': 'genesis.',
     '25': 'genesis.',
     '41': 'genesis.' },
  answers: 
   [ { NAME: { name: 'genesis.', type: 1, class: 1 },
       TTL: 60,
       RDLENGTH: 4,
       DATA: { integer: 2130706433, string: '127.0.0.1' } },
     { NAME: { name: 'genesis.', type: 1, class: 1 },
       TTL: 60,
       RDLENGTH: 4,
       DATA: { integer: 3397978090, string: '202.137.7.234' } } ],
  authorities: [],
  additionals: [] }
response from server


  */
