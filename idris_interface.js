var IdrisInterface = function(element) {
	this.callbacks_ = [];
	this.events_ = [];
	this.element_ = element;

	var that = this;
	element.addEventListener('keydown', function(e) {that.on_keydown_(e)});
}

IdrisInterface.prototype.on_keydown_ = function(e) {
	if (this.callbacks_.length > 0) {
		this.callbacks_.shift()(e['keyCode']);
	} else {
		this.events_.push(e);
	}
}

IdrisInterface.prototype.add_callback = function(callback) {
	if (this.events_.length > 0) {
		var e = this.events_.shift();
		callback(this.events_.shift());	
	} else {
		this.callbacks_.push(callback);
	}	
}

IdrisInterface.prototype.show = function(str) {
	this.element_.innerHTML = str;
}

var idris_interface = new IdrisInterface(document.getElementById('game-area'));
