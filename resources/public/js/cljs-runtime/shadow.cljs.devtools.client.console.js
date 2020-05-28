goog.provide('shadow.cljs.devtools.client.console');
goog.require('cljs.core');
goog.require('clojure.string');
shadow.cljs.devtools.client.console.push_all = (function shadow$cljs$devtools$client$console$push_all(arr,item){
if(cljs.core.vector_QMARK_(item)){
var seq__3655 = cljs.core.seq(item);
var chunk__3656 = null;
var count__3657 = (0);
var i__3658 = (0);
while(true){
if((i__3658 < count__3657)){
var it = chunk__3656.cljs$core$IIndexed$_nth$arity$2(null,i__3658);
arr.push(it);


var G__3659 = seq__3655;
var G__3660 = chunk__3656;
var G__3661 = count__3657;
var G__3662 = (i__3658 + (1));
seq__3655 = G__3659;
chunk__3656 = G__3660;
count__3657 = G__3661;
i__3658 = G__3662;
continue;
} else {
var temp__5457__auto__ = cljs.core.seq(seq__3655);
if(temp__5457__auto__){
var seq__3655__$1 = temp__5457__auto__;
if(cljs.core.chunked_seq_QMARK_(seq__3655__$1)){
var c__4351__auto__ = cljs.core.chunk_first(seq__3655__$1);
var G__3663 = cljs.core.chunk_rest(seq__3655__$1);
var G__3664 = c__4351__auto__;
var G__3665 = cljs.core.count(c__4351__auto__);
var G__3666 = (0);
seq__3655 = G__3663;
chunk__3656 = G__3664;
count__3657 = G__3665;
i__3658 = G__3666;
continue;
} else {
var it = cljs.core.first(seq__3655__$1);
arr.push(it);


var G__3667 = cljs.core.next(seq__3655__$1);
var G__3668 = null;
var G__3669 = (0);
var G__3670 = (0);
seq__3655 = G__3667;
chunk__3656 = G__3668;
count__3657 = G__3669;
i__3658 = G__3670;
continue;
}
} else {
return null;
}
}
break;
}
} else {
return arr.push(item);
}
});
shadow.cljs.devtools.client.console.object_ref = (function shadow$cljs$devtools$client$console$object_ref(obj){
if(cljs.core.truth_(obj)){
return ["object",({"object": obj})];
} else {
return null;
}
});
shadow.cljs.devtools.client.console.map__GT_style = (function shadow$cljs$devtools$client$console$map__GT_style(m){
return ({"style": clojure.string.join.cljs$core$IFn$_invoke$arity$2("",cljs.core.map.cljs$core$IFn$_invoke$arity$2((function (p__3671){
var vec__3672 = p__3671;
var k = cljs.core.nth.cljs$core$IFn$_invoke$arity$3(vec__3672,(0),null);
var v = cljs.core.nth.cljs$core$IFn$_invoke$arity$3(vec__3672,(1),null);
return [cljs.core.str.cljs$core$IFn$_invoke$arity$1(cljs.core.name(k)),": ",cljs.core.str.cljs$core$IFn$_invoke$arity$1(v),";"].join('');
}),m))});
});
shadow.cljs.devtools.client.console.clj__GT_jsonml = (function shadow$cljs$devtools$client$console$clj__GT_jsonml(struct){
if((struct == null)){
return null;
} else {
if(cljs.core.array_QMARK_(struct)){
return struct;
} else {
if(cljs.core.vector_QMARK_(struct)){
var vec__3675 = struct;
var seq__3676 = cljs.core.seq(vec__3675);
var first__3677 = cljs.core.first(seq__3676);
var seq__3676__$1 = cljs.core.next(seq__3676);
var tag = first__3677;
var first__3677__$1 = cljs.core.first(seq__3676__$1);
var seq__3676__$2 = cljs.core.next(seq__3676__$1);
var attrs = first__3677__$1;
var children = seq__3676__$2;
var js = [cljs.core.name(tag),shadow.cljs.devtools.client.console.map__GT_style(attrs)];
var seq__3678_3682 = cljs.core.seq(children);
var chunk__3679_3683 = null;
var count__3680_3684 = (0);
var i__3681_3685 = (0);
while(true){
if((i__3681_3685 < count__3680_3684)){
var child_3686 = chunk__3679_3683.cljs$core$IIndexed$_nth$arity$2(null,i__3681_3685);
shadow.cljs.devtools.client.console.push_all(js,(shadow.cljs.devtools.client.console.clj__GT_jsonml.cljs$core$IFn$_invoke$arity$1 ? shadow.cljs.devtools.client.console.clj__GT_jsonml.cljs$core$IFn$_invoke$arity$1(child_3686) : shadow.cljs.devtools.client.console.clj__GT_jsonml.call(null,child_3686)));


var G__3687 = seq__3678_3682;
var G__3688 = chunk__3679_3683;
var G__3689 = count__3680_3684;
var G__3690 = (i__3681_3685 + (1));
seq__3678_3682 = G__3687;
chunk__3679_3683 = G__3688;
count__3680_3684 = G__3689;
i__3681_3685 = G__3690;
continue;
} else {
var temp__5457__auto___3691 = cljs.core.seq(seq__3678_3682);
if(temp__5457__auto___3691){
var seq__3678_3692__$1 = temp__5457__auto___3691;
if(cljs.core.chunked_seq_QMARK_(seq__3678_3692__$1)){
var c__4351__auto___3693 = cljs.core.chunk_first(seq__3678_3692__$1);
var G__3694 = cljs.core.chunk_rest(seq__3678_3692__$1);
var G__3695 = c__4351__auto___3693;
var G__3696 = cljs.core.count(c__4351__auto___3693);
var G__3697 = (0);
seq__3678_3682 = G__3694;
chunk__3679_3683 = G__3695;
count__3680_3684 = G__3696;
i__3681_3685 = G__3697;
continue;
} else {
var child_3698 = cljs.core.first(seq__3678_3692__$1);
shadow.cljs.devtools.client.console.push_all(js,(shadow.cljs.devtools.client.console.clj__GT_jsonml.cljs$core$IFn$_invoke$arity$1 ? shadow.cljs.devtools.client.console.clj__GT_jsonml.cljs$core$IFn$_invoke$arity$1(child_3698) : shadow.cljs.devtools.client.console.clj__GT_jsonml.call(null,child_3698)));


var G__3699 = cljs.core.next(seq__3678_3692__$1);
var G__3700 = null;
var G__3701 = (0);
var G__3702 = (0);
seq__3678_3682 = G__3699;
chunk__3679_3683 = G__3700;
count__3680_3684 = G__3701;
i__3681_3685 = G__3702;
continue;
}
} else {
}
}
break;
}

return js;
} else {
if(typeof struct === 'string'){
return struct;
} else {
if(typeof struct === 'number'){
return struct;
} else {
if(cljs.core.seq_QMARK_(struct)){
return cljs.core.into.cljs$core$IFn$_invoke$arity$3(cljs.core.PersistentVector.EMPTY,cljs.core.map.cljs$core$IFn$_invoke$arity$1(shadow.cljs.devtools.client.console.clj__GT_jsonml),struct);
} else {
return shadow.cljs.devtools.client.console.object_ref(struct);

}
}
}
}
}
}
});

/**
* @constructor
*/
shadow.cljs.devtools.client.console.SeqFormatter = (function (){
});
shadow.cljs.devtools.client.console.SeqFormatter.prototype.shadow$formatter = (function (){
var self__ = this;
var this$ = this;
return true;
});

shadow.cljs.devtools.client.console.SeqFormatter.prototype.header = (function (obj){
var self__ = this;
var this$ = this;
if(((cljs.core.sequential_QMARK_(obj)) || (cljs.core.set_QMARK_(obj)))){
return shadow.cljs.devtools.client.console.clj__GT_jsonml(new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"span","span",1394872991),cljs.core.PersistentArrayMap.EMPTY,[cljs.core.str.cljs$core$IFn$_invoke$arity$1(cljs.core.pr_str.cljs$core$IFn$_invoke$arity$variadic(cljs.core.prim_seq.cljs$core$IFn$_invoke$arity$2([cljs.core.type(obj)], 0)))," [count: ",cljs.core.str.cljs$core$IFn$_invoke$arity$1(cljs.core.count(obj)),"]"].join('')], null));
} else {
return null;
}
});

shadow.cljs.devtools.client.console.SeqFormatter.prototype.hasBody = (function (obj){
var self__ = this;
var this$ = this;
return cljs.core.boolean$(cljs.core.seq(obj));
});

shadow.cljs.devtools.client.console.SeqFormatter.prototype.body = (function (s){
var self__ = this;
var this$ = this;
return shadow.cljs.devtools.client.console.clj__GT_jsonml(new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"ol","ol",932524051),new cljs.core.PersistentArrayMap(null, 1, [new cljs.core.Keyword(null,"margin","margin",-995903681),(0)], null),(function (){var iter__4324__auto__ = ((function (this$){
return (function shadow$cljs$devtools$client$console$iter__3703(s__3704){
return (new cljs.core.LazySeq(null,((function (this$){
return (function (){
var s__3704__$1 = s__3704;
while(true){
var temp__5457__auto__ = cljs.core.seq(s__3704__$1);
if(temp__5457__auto__){
var s__3704__$2 = temp__5457__auto__;
if(cljs.core.chunked_seq_QMARK_(s__3704__$2)){
var c__4322__auto__ = cljs.core.chunk_first(s__3704__$2);
var size__4323__auto__ = cljs.core.count(c__4322__auto__);
var b__3706 = cljs.core.chunk_buffer(size__4323__auto__);
if((function (){var i__3705 = (0);
while(true){
if((i__3705 < size__4323__auto__)){
var value = cljs.core._nth.cljs$core$IFn$_invoke$arity$2(c__4322__auto__,i__3705);
cljs.core.chunk_append(b__3706,new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"li","li",723558921),cljs.core.PersistentArrayMap.EMPTY,shadow.cljs.devtools.client.console.object_ref(value)], null));

var G__3707 = (i__3705 + (1));
i__3705 = G__3707;
continue;
} else {
return true;
}
break;
}
})()){
return cljs.core.chunk_cons(cljs.core.chunk(b__3706),shadow$cljs$devtools$client$console$iter__3703(cljs.core.chunk_rest(s__3704__$2)));
} else {
return cljs.core.chunk_cons(cljs.core.chunk(b__3706),null);
}
} else {
var value = cljs.core.first(s__3704__$2);
return cljs.core.cons(new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"li","li",723558921),cljs.core.PersistentArrayMap.EMPTY,shadow.cljs.devtools.client.console.object_ref(value)], null),shadow$cljs$devtools$client$console$iter__3703(cljs.core.rest(s__3704__$2)));
}
} else {
return null;
}
break;
}
});})(this$))
,null,null));
});})(this$))
;
return iter__4324__auto__(s);
})()], null));
});

shadow.cljs.devtools.client.console.SeqFormatter.getBasis = (function (){
return cljs.core.PersistentVector.EMPTY;
});

shadow.cljs.devtools.client.console.SeqFormatter.cljs$lang$type = true;

shadow.cljs.devtools.client.console.SeqFormatter.cljs$lang$ctorStr = "shadow.cljs.devtools.client.console/SeqFormatter";

shadow.cljs.devtools.client.console.SeqFormatter.cljs$lang$ctorPrWriter = (function (this__4192__auto__,writer__4193__auto__,opt__4194__auto__){
return cljs.core._write(writer__4193__auto__,"shadow.cljs.devtools.client.console/SeqFormatter");
});

/**
 * Positional factory function for shadow.cljs.devtools.client.console/SeqFormatter.
 */
shadow.cljs.devtools.client.console.__GT_SeqFormatter = (function shadow$cljs$devtools$client$console$__GT_SeqFormatter(){
return (new shadow.cljs.devtools.client.console.SeqFormatter());
});


/**
* @constructor
*/
shadow.cljs.devtools.client.console.MapFormatter = (function (){
});
shadow.cljs.devtools.client.console.MapFormatter.prototype.shadow$formatter = (function (){
var self__ = this;
var this$ = this;
return true;
});

shadow.cljs.devtools.client.console.MapFormatter.prototype.header = (function (obj){
var self__ = this;
var this$ = this;
if((((obj instanceof cljs.core.PersistentHashMap)) || ((obj instanceof cljs.core.PersistentArrayMap)) || (cljs.core.record_QMARK_(obj)))){
return shadow.cljs.devtools.client.console.clj__GT_jsonml(new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"span","span",1394872991),cljs.core.PersistentArrayMap.EMPTY,[cljs.core.str.cljs$core$IFn$_invoke$arity$1(cljs.core.pr_str.cljs$core$IFn$_invoke$arity$variadic(cljs.core.prim_seq.cljs$core$IFn$_invoke$arity$2([cljs.core.type(obj)], 0)))," [count: ",cljs.core.str.cljs$core$IFn$_invoke$arity$1(cljs.core.count(obj)),"]"].join('')], null));
} else {
return null;
}
});

shadow.cljs.devtools.client.console.MapFormatter.prototype.hasBody = (function (obj){
var self__ = this;
var this$ = this;
return cljs.core.boolean$(cljs.core.seq(obj));
});

shadow.cljs.devtools.client.console.MapFormatter.prototype.body = (function (m){
var self__ = this;
var this$ = this;
return shadow.cljs.devtools.client.console.clj__GT_jsonml(new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"table","table",-564943036),new cljs.core.PersistentArrayMap(null, 2, [new cljs.core.Keyword(null,"width","width",-384071477),"100%",new cljs.core.Keyword(null,"margin-left","margin-left",2015598377),"14px"], null),(function (){var iter__4324__auto__ = ((function (this$){
return (function shadow$cljs$devtools$client$console$iter__3708(s__3709){
return (new cljs.core.LazySeq(null,((function (this$){
return (function (){
var s__3709__$1 = s__3709;
while(true){
var temp__5457__auto__ = cljs.core.seq(s__3709__$1);
if(temp__5457__auto__){
var s__3709__$2 = temp__5457__auto__;
if(cljs.core.chunked_seq_QMARK_(s__3709__$2)){
var c__4322__auto__ = cljs.core.chunk_first(s__3709__$2);
var size__4323__auto__ = cljs.core.count(c__4322__auto__);
var b__3711 = cljs.core.chunk_buffer(size__4323__auto__);
if((function (){var i__3710 = (0);
while(true){
if((i__3710 < size__4323__auto__)){
var key = cljs.core._nth.cljs$core$IFn$_invoke$arity$2(c__4322__auto__,i__3710);
var value = cljs.core.get.cljs$core$IFn$_invoke$arity$2(m,key);
cljs.core.chunk_append(b__3711,new cljs.core.PersistentVector(null, 4, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"tr","tr",-1424774646),new cljs.core.PersistentArrayMap(null, 1, [new cljs.core.Keyword(null,"vertical-align","vertical-align",651007333),"top"], null),new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"td","td",1479933353),cljs.core.PersistentArrayMap.EMPTY,shadow.cljs.devtools.client.console.object_ref(key)], null),new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"td","td",1479933353),cljs.core.PersistentArrayMap.EMPTY,shadow.cljs.devtools.client.console.object_ref(value)], null)], null));

var G__3713 = (i__3710 + (1));
i__3710 = G__3713;
continue;
} else {
return true;
}
break;
}
})()){
return cljs.core.chunk_cons(cljs.core.chunk(b__3711),shadow$cljs$devtools$client$console$iter__3708(cljs.core.chunk_rest(s__3709__$2)));
} else {
return cljs.core.chunk_cons(cljs.core.chunk(b__3711),null);
}
} else {
var key = cljs.core.first(s__3709__$2);
var value = cljs.core.get.cljs$core$IFn$_invoke$arity$2(m,key);
return cljs.core.cons(new cljs.core.PersistentVector(null, 4, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"tr","tr",-1424774646),new cljs.core.PersistentArrayMap(null, 1, [new cljs.core.Keyword(null,"vertical-align","vertical-align",651007333),"top"], null),new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"td","td",1479933353),cljs.core.PersistentArrayMap.EMPTY,shadow.cljs.devtools.client.console.object_ref(key)], null),new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"td","td",1479933353),cljs.core.PersistentArrayMap.EMPTY,shadow.cljs.devtools.client.console.object_ref(value)], null)], null),shadow$cljs$devtools$client$console$iter__3708(cljs.core.rest(s__3709__$2)));
}
} else {
return null;
}
break;
}
});})(this$))
,null,null));
});})(this$))
;
return iter__4324__auto__((function (){var k = cljs.core.keys(m);
try{return cljs.core.sort.cljs$core$IFn$_invoke$arity$1(k);
}catch (e3712){var e = e3712;
return k;
}})());
})()], null));
});

shadow.cljs.devtools.client.console.MapFormatter.getBasis = (function (){
return cljs.core.PersistentVector.EMPTY;
});

shadow.cljs.devtools.client.console.MapFormatter.cljs$lang$type = true;

shadow.cljs.devtools.client.console.MapFormatter.cljs$lang$ctorStr = "shadow.cljs.devtools.client.console/MapFormatter";

shadow.cljs.devtools.client.console.MapFormatter.cljs$lang$ctorPrWriter = (function (this__4192__auto__,writer__4193__auto__,opt__4194__auto__){
return cljs.core._write(writer__4193__auto__,"shadow.cljs.devtools.client.console/MapFormatter");
});

/**
 * Positional factory function for shadow.cljs.devtools.client.console/MapFormatter.
 */
shadow.cljs.devtools.client.console.__GT_MapFormatter = (function shadow$cljs$devtools$client$console$__GT_MapFormatter(){
return (new shadow.cljs.devtools.client.console.MapFormatter());
});

shadow.cljs.devtools.client.console.keyword_style = new cljs.core.PersistentArrayMap(null, 1, [new cljs.core.Keyword(null,"color","color",1011675173),"rgb(136, 19, 145)"], null);

/**
* @constructor
*/
shadow.cljs.devtools.client.console.KeywordFormatter = (function (){
});
shadow.cljs.devtools.client.console.KeywordFormatter.prototype.shadow$formatter = (function (){
var self__ = this;
var this$ = this;
return true;
});

shadow.cljs.devtools.client.console.KeywordFormatter.prototype.header = (function (obj){
var self__ = this;
var this$ = this;
if((obj instanceof cljs.core.Keyword)){
return shadow.cljs.devtools.client.console.clj__GT_jsonml(new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"span","span",1394872991),shadow.cljs.devtools.client.console.keyword_style,cljs.core.pr_str.cljs$core$IFn$_invoke$arity$variadic(cljs.core.prim_seq.cljs$core$IFn$_invoke$arity$2([obj], 0))], null));
} else {
return null;
}
});

shadow.cljs.devtools.client.console.KeywordFormatter.prototype.hasBody = (function (obj){
var self__ = this;
var this$ = this;
return false;
});

shadow.cljs.devtools.client.console.KeywordFormatter.prototype.body = (function (m){
var self__ = this;
var this$ = this;
return null;
});

shadow.cljs.devtools.client.console.KeywordFormatter.getBasis = (function (){
return cljs.core.PersistentVector.EMPTY;
});

shadow.cljs.devtools.client.console.KeywordFormatter.cljs$lang$type = true;

shadow.cljs.devtools.client.console.KeywordFormatter.cljs$lang$ctorStr = "shadow.cljs.devtools.client.console/KeywordFormatter";

shadow.cljs.devtools.client.console.KeywordFormatter.cljs$lang$ctorPrWriter = (function (this__4192__auto__,writer__4193__auto__,opt__4194__auto__){
return cljs.core._write(writer__4193__auto__,"shadow.cljs.devtools.client.console/KeywordFormatter");
});

/**
 * Positional factory function for shadow.cljs.devtools.client.console/KeywordFormatter.
 */
shadow.cljs.devtools.client.console.__GT_KeywordFormatter = (function shadow$cljs$devtools$client$console$__GT_KeywordFormatter(){
return (new shadow.cljs.devtools.client.console.KeywordFormatter());
});


/**
* @constructor
*/
shadow.cljs.devtools.client.console.SymbolFormatter = (function (){
});
shadow.cljs.devtools.client.console.SymbolFormatter.prototype.shadow$formatter = (function (){
var self__ = this;
var this$ = this;
return true;
});

shadow.cljs.devtools.client.console.SymbolFormatter.prototype.header = (function (obj){
var self__ = this;
var this$ = this;
if((obj instanceof cljs.core.Symbol)){
return shadow.cljs.devtools.client.console.clj__GT_jsonml(new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"span","span",1394872991),shadow.cljs.devtools.client.console.keyword_style,cljs.core.pr_str.cljs$core$IFn$_invoke$arity$variadic(cljs.core.prim_seq.cljs$core$IFn$_invoke$arity$2([obj], 0))], null));
} else {
return null;
}
});

shadow.cljs.devtools.client.console.SymbolFormatter.prototype.hasBody = (function (obj){
var self__ = this;
var this$ = this;
return false;
});

shadow.cljs.devtools.client.console.SymbolFormatter.prototype.body = (function (m){
var self__ = this;
var this$ = this;
return null;
});

shadow.cljs.devtools.client.console.SymbolFormatter.getBasis = (function (){
return cljs.core.PersistentVector.EMPTY;
});

shadow.cljs.devtools.client.console.SymbolFormatter.cljs$lang$type = true;

shadow.cljs.devtools.client.console.SymbolFormatter.cljs$lang$ctorStr = "shadow.cljs.devtools.client.console/SymbolFormatter";

shadow.cljs.devtools.client.console.SymbolFormatter.cljs$lang$ctorPrWriter = (function (this__4192__auto__,writer__4193__auto__,opt__4194__auto__){
return cljs.core._write(writer__4193__auto__,"shadow.cljs.devtools.client.console/SymbolFormatter");
});

/**
 * Positional factory function for shadow.cljs.devtools.client.console/SymbolFormatter.
 */
shadow.cljs.devtools.client.console.__GT_SymbolFormatter = (function shadow$cljs$devtools$client$console$__GT_SymbolFormatter(){
return (new shadow.cljs.devtools.client.console.SymbolFormatter());
});


/**
* @constructor
*/
shadow.cljs.devtools.client.console.DerefFormatter = (function (){
});
shadow.cljs.devtools.client.console.DerefFormatter.prototype.shadow$formatter = (function (){
var self__ = this;
var this$ = this;
return true;
});

shadow.cljs.devtools.client.console.DerefFormatter.prototype.header = (function (obj){
var self__ = this;
var this$ = this;
if((((obj instanceof cljs.core.Atom)) || ((obj instanceof cljs.core.Volatile)))){
return shadow.cljs.devtools.client.console.clj__GT_jsonml(new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"span","span",1394872991),shadow.cljs.devtools.client.console.keyword_style,["@DEREF ",cljs.core.str.cljs$core$IFn$_invoke$arity$1(cljs.core.pr_str.cljs$core$IFn$_invoke$arity$variadic(cljs.core.prim_seq.cljs$core$IFn$_invoke$arity$2([cljs.core.type(obj)], 0)))].join('')], null));
} else {
return null;
}
});

shadow.cljs.devtools.client.console.DerefFormatter.prototype.hasBody = (function (obj){
var self__ = this;
var this$ = this;
return true;
});

shadow.cljs.devtools.client.console.DerefFormatter.prototype.body = (function (v){
var self__ = this;
var this$ = this;
return shadow.cljs.devtools.client.console.clj__GT_jsonml(new cljs.core.PersistentVector(null, 3, 5, cljs.core.PersistentVector.EMPTY_NODE, [new cljs.core.Keyword(null,"div","div",1057191632),new cljs.core.PersistentArrayMap(null, 1, [new cljs.core.Keyword(null,"margin-left","margin-left",2015598377),"14px"], null),shadow.cljs.devtools.client.console.object_ref(cljs.core.deref(v))], null));
});

shadow.cljs.devtools.client.console.DerefFormatter.getBasis = (function (){
return cljs.core.PersistentVector.EMPTY;
});

shadow.cljs.devtools.client.console.DerefFormatter.cljs$lang$type = true;

shadow.cljs.devtools.client.console.DerefFormatter.cljs$lang$ctorStr = "shadow.cljs.devtools.client.console/DerefFormatter";

shadow.cljs.devtools.client.console.DerefFormatter.cljs$lang$ctorPrWriter = (function (this__4192__auto__,writer__4193__auto__,opt__4194__auto__){
return cljs.core._write(writer__4193__auto__,"shadow.cljs.devtools.client.console/DerefFormatter");
});

/**
 * Positional factory function for shadow.cljs.devtools.client.console/DerefFormatter.
 */
shadow.cljs.devtools.client.console.__GT_DerefFormatter = (function shadow$cljs$devtools$client$console$__GT_DerefFormatter(){
return (new shadow.cljs.devtools.client.console.DerefFormatter());
});

shadow.cljs.devtools.client.console.install_all_BANG_ = (function shadow$cljs$devtools$client$console$install_all_BANG_(){
var temp__5457__auto__ = goog.global.devtoolsFormatters;
if(cljs.core.truth_(temp__5457__auto__)){
var f = temp__5457__auto__;
var G__3714 = f;
G__3714.push((new shadow.cljs.devtools.client.console.KeywordFormatter()));

G__3714.push((new shadow.cljs.devtools.client.console.MapFormatter()));

G__3714.push((new shadow.cljs.devtools.client.console.SeqFormatter()));

G__3714.push((new shadow.cljs.devtools.client.console.SymbolFormatter()));

G__3714.push((new shadow.cljs.devtools.client.console.DerefFormatter()));

return G__3714;
} else {
return null;
}
});
shadow.cljs.devtools.client.console.remove_all_BANG_ = (function shadow$cljs$devtools$client$console$remove_all_BANG_(){
var all = cljs.core.into_array.cljs$core$IFn$_invoke$arity$1(cljs.core.remove.cljs$core$IFn$_invoke$arity$2((function (p1__3715_SHARP_){
return goog.object.get(p1__3715_SHARP_,"shadow$formatter");
}),cljs.core.array_seq.cljs$core$IFn$_invoke$arity$1((function (){var or__3949__auto__ = goog.global.devtoolsFormatters;
if(cljs.core.truth_(or__3949__auto__)){
return or__3949__auto__;
} else {
return [];
}
})())));
return goog.object.set(goog.global,"devtoolsFormatters",all);
});
shadow.cljs.devtools.client.console.remove_all_BANG_();
shadow.cljs.devtools.client.console.install_all_BANG_();

//# sourceMappingURL=shadow.cljs.devtools.client.console.js.map
